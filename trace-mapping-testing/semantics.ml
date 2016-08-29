open Traces

type op = Eq | Seq | Add
type expr = (* e *)
  | EVal of int                              (* i *)
  | EOp of expr * op * expr (* e₁ ⊗ e₂ *)
  | EIfThenElse of expr * expr * expr        (* if e then e₁ else e₂ *)
  | ELoad of int * expr                      (* b[e] *)
  | EStore of int * expr * expr              (* b[e] := e *)
  | ECall of int * int * expr                (* C.P(e) *)
  | EExit                                    (* exit *)
type component_interface =
    { name: int; import: (int * int) list; export: int }
type component =
    { name: int; export: int; procs: expr array; bufs: int array array }
type attacker_interface = component_interface list
type attacker = component list

type flatevalcon =
| CHoleOp of op * expr
| COpHole of int * op
| CIfHoleThenElse of expr * expr
| CHoleLoad of int
| CHoleStore of int * expr
| CStoreHole of int * int
| CCallHole of int * int
type evalcon = flatevalcon list
type cfg_state = (int * int array array) list

type basic_stack = (int * int * evalcon) list
type basic_cfg = int * cfg_state * basic_stack * evalcon * expr

type prg_cfg_stack =
  | PrgBase of basic_stack
  | PrgAppend of basic_stack * ctx_cfg_stack
 and ctx_cfg_stack =
   | CtxBase
   | CtxAppend of prg_cfg_stack
type cfg =
  | PrgCfg of int * cfg_state * prg_cfg_stack * evalcon * expr
  | CtxCfg of cfg_state * ctx_cfg_stack
  | ExitCfg

let c_main = 0
let p_main = 0

let apply_op i1 op i2 = match op with
  | Eq -> if i1 = i2 then 1 else 0
  | Seq -> i2
  | Add -> i1 + i2

let fetch (s: cfg_state) c b i: int =
  let s_c = List.assoc c s in
  s_c.(b).(i)

let update (s: cfg_state) c b i1 i2: cfg_state =
  let s_c = List.assoc c s in
  let s'_c = Array.init (Array.length s_c) (fun i -> Array.copy s_c.(i)) in
  s'_c.(b).(i1) <- i2;
  (c, s'_c) :: (List.remove_assoc c s)

let basic_step (delta: ((int * int) * expr) list) (cfg: basic_cfg): basic_cfg =
  match cfg with
  | (c, s, sigma, k, EOp (e1, op, e2)) ->
     (c, s, sigma, CHoleOp (op, e2) :: k, e1)
  | (c, s, sigma, CHoleOp (op, e2) :: k, EVal i1) ->
     (c, s, sigma, COpHole (i1, op) :: k, e2)
  | (c, s, sigma, COpHole (i1, op) :: k, EVal i2) ->
     (c, s, sigma, k, EVal (apply_op i1 op i2))
  | (c, s, sigma, k, EIfThenElse (e1, e2, e3)) ->
     (c, s, sigma, CIfHoleThenElse (e2, e3) :: k, e1)
  | (c, s, sigma, CIfHoleThenElse (e2, e3) :: k, EVal 0) ->
     (c, s, sigma, k, e3)
  | (c, s, sigma, CIfHoleThenElse (e2, e3) :: k, EVal _) ->
     (c, s, sigma, k, e2)
  | (c, s, sigma, k, ELoad (b, e)) ->
     (c, s, sigma, CHoleLoad b :: k, e)
  | (c, s, sigma, CHoleLoad b :: k, EVal i) ->
     (c, s, sigma, k, EVal (fetch s c b i))
  | (c, s, sigma, k, EStore (b, e1, e2)) ->
     (c, s, sigma, CHoleStore (b, e2) :: k, e1)
  | (c, s, sigma, CHoleStore (b, e2) :: k, EVal i1) ->
     (c, s, sigma, CStoreHole (b, i1) :: k, e2)
  | (c, s, sigma, CStoreHole (b, i1) :: k, EVal i2) ->
     let s' = update s c b i1 i2 in
     (c, s', sigma, k, EVal i2)
  | (c, s, sigma, k, ECall (c', p', e)) ->
     (c, s, sigma, CCallHole (c', p') :: k, e)
  | (c, s, sigma, CCallHole (c', p') :: k, EVal i) ->
     let e_p = List.assoc (c', p') delta in
     let i_a = fetch s c 0 0 in
     let s' = update s c' 0 0 i in
     let sigma' = ((c,i_a,k) :: sigma) in
     (c', s', sigma', [], e_p)
  | (c, s, (c',i_a,k) :: sigma', [], EVal i) ->
     let s' = update s c' 0 0 i_a in
     (c', s', sigma', k, EVal i)
  | (_, _, _, [], EVal _)
  | (_, _, _, _, EExit) ->
     failwith "attempt to reduce a final configuration"

let prg_top psigma =
  match psigma with
  | PrgBase x -> x
  | PrgAppend (x, _) -> x

let prg_set_top psigma y =
  match psigma with
  | PrgBase _ -> PrgBase y
  | PrgAppend (_, t) -> PrgAppend (y, t)

let reduces_with (delta: ((int * int) * expr) list) (cfg: cfg) (alpha: alpha): cfg option =
  let internal_step () =
    match cfg with
    | PrgCfg (c,s,psigma,k,e) ->
       let (c',s',sigma', k', e') = basic_step delta (c,s,prg_top psigma,k,e) in
       PrgCfg (c',s',prg_set_top psigma sigma', k', e')
    | _ -> cfg
  in
  match alpha with
  (* 1 - Internal program reductions *)
  | Int (IntCall (c'',p''), Prg) ->
     begin
       match cfg with
       | PrgCfg (_, _, _, CCallHole (c', p') :: _, EVal _) ->
	  if c' = c'' && p' = p'' && List.mem_assoc (c', p') delta then
	    Some (internal_step ())
	  else
	    None
       | _ ->
	  None
     end
  | Int (IntRet, Prg) ->
     begin
       match cfg with
       | PrgCfg (_, _, psigma, [], EVal _) ->
	  if prg_top psigma <> [] then
	    Some (internal_step ())
	  else
	    None
       | _ ->
	  None
     end
  | Int (IntTau, Prg) ->
     begin
       match cfg with
       | PrgCfg (_, _, _, CCallHole (_, _) :: _, EVal _)
       | PrgCfg (_, _, _, [], EVal _)
       | PrgCfg (_, _, _, _, EExit) ->
	  None
       | PrgCfg _ ->
	  Some (internal_step ())
       | _ ->
	  None
     end
  (* 2 - Internal context reductions *)
  | Int (_, Ctx) ->
     begin
       match cfg with
       | CtxCfg _ -> Some cfg
       | _ -> None
     end
  (* 3 - Call from context code from program code *)
  | Ext (ExtCall (c', p', i), Ctx) ->
     begin
       match cfg with
       | CtxCfg (s, csigma) ->
	  if List.mem_assoc (c', p') delta then
	    let e_p = List.assoc (c', p') delta in
	    let s' = update s c' 0 0 i in
	    Some (PrgCfg (c', s', PrgAppend ([], csigma), [], e_p))
	  else
	    None
       | _ -> None
     end
  (* 4 - Return from context code to program code *)
  | Ext (ExtRet i, Ctx) ->
     begin
       match cfg with
       | CtxCfg (s, CtxAppend psigma) ->
	  begin
	    match prg_top psigma with
	    | (c', i_a, k) :: sigma' ->
	       let s' = update s c' 0 0 i_a in
	       Some (PrgCfg (c', s', prg_set_top psigma sigma', k, EVal i))
	    | _ -> None
	  end
       | _ -> None
     end
  (* 5 - Call from program code to context code *)
  | Ext (ExtCall (c'',p'',i''), Prg) ->
     begin
       match cfg with
       | PrgCfg (c, s, psigma, CCallHole (c', p') :: k, EVal i') ->
	  if c' = c'' && p' = p'' && i' = i'' && not (List.mem_assoc (c', p') delta) then
	    let i_a = fetch s c 0 0 in
	    let psigma' = prg_set_top psigma ((c, i_a, k) :: prg_top psigma) in
	    Some (CtxCfg (s, CtxAppend psigma'))
	  else
	    None
       | _ ->
	  None
     end
  (* 6 - Return from program code to context code *)
  | Ext (ExtRet i', Prg) ->
     begin
       match cfg with
       | PrgCfg (_, s, PrgAppend ([], csigma), [], EVal i) ->
	  if i = i' then
	    Some (CtxCfg (s, csigma))
	  else
	    None
       | _ ->
	  None
     end
  (* 7 - Termination from context code *)
  | Ext (Term, Ctx) ->
     begin
       match cfg with
       | CtxCfg _ -> Some ExitCfg
       | _ -> None
     end
  (* 8 - Termination from program code *)
  | Ext (Term, Prg) ->
     begin
       match cfg with
       | PrgCfg (_, _, PrgBase [], [], EVal _) ->
	  Some ExitCfg
       | PrgCfg (_, _, _, _, EExit) ->
	  Some ExitCfg
       | _ ->
	  None
     end

let procbodies att =
  List.concat (List.map
		 (fun component ->
		  Array.to_list
		    (Array.mapi
		       (fun i e -> ((component.name,i),e))
		       component.procs))
		 att)

let initcfg att =
  let initstate = List.map (fun component -> (component.name, component.bufs)) att in
  try let component = List.find (fun component -> component.name = c_main) att in
     PrgCfg (c_main, initstate, PrgBase [], [], component.procs.(0))
  with
  | Not_found ->
     CtxCfg (initstate, CtxBase)

let has_trace att (t0: trace): bool =
  let delta = procbodies att in
  let rec aux cfg t =
    match reduces_with delta cfg (Int (IntTau, Prg)) with
    | Some cfg' ->
       aux cfg' t
    | None ->
       begin
	 match t with
	 | [] -> true
	 | (Int (IntTau, Prg)) :: t' ->
	    aux cfg t'
	 | alpha :: t' ->
	    begin
	      match reduces_with delta cfg alpha with
	      | Some cfg' ->
		 aux cfg' t'
	      | None ->
		 false
	    end
       end
  in
  aux (initcfg att) t0
