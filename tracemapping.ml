(* Trace mapping algorithm *)

(* Trace syntax *)
type origin = Ctx | Prg
type internal_action = (* ia *)
  | IntCall of int * int (* C.P(/) *)
  | IntRet               (* Ret / *)
type external_action = (* ea *)
  | ExtCall of int * int * int (* C.P(reg) with r≠r_com ⇒ reg[r]=0 *)
  | ExtRet of int              (* Ret reg  with r≠r_com ⇒ reg[r]=0 *)
  | Term                       (* ✓ *)
type action = (* α *)
  | Int of internal_action * origin (* Iα *)
  | Ext of external_action * origin (* Eα *)
type trace = action list

(* Goal: Given a trace t and a program action prg_a,
         given P and Q that both have trace t,
         given that P has trace t.prg_a! and Q doesn't have it,
         given that Q doesn't have trace t.✓!,
         produce a high-level attacker that distinguishes P from Q
         with pre-supplied component interfaces. *)

(* Idea: On paths t.prg_a'! with prg_a' ∉ {✓, prg_a}, the high-level
         attacker will diverge by producing an internal infinite
         loop.
         On path t.prg_a, the attacker will terminate the program and
         lead to t.prg_a.✓?, unless the program already terminates by
         himself (case prg_a = ✓).

         When interacting with P, either prg_a = ✓ and the program
         terminates, or prg_a ≠ ✓ and yields back control to the
         context who can thus terminate.
         When interacting with Q, Q will either diverge or produce a
         non-terminating action that yields control back to the
         context, who will diverge. *)

(* Macro instructions later mapped to high-level expressions *)
type macro =
  | MCall of int * int * int
  | MRet of int
  | MCheckCall of int * int * int * int
  | MCheckArg of int
  | MDiverge
type code = macro list
type proc_call_descr = int * int * int * code
type state = int * proc_call_descr list * proc_call_descr list

(* Map trace to pseudo-code *)

let c_main = 0
let p_main = 0

let initial_state (t: trace): state =
  (* initial state when the program starts computation *)
  let st0_prg = (0, [], []) in
  (* initial state when the context starts computation *)
  let st0_ctx = (0, [(c_main, p_main, -1, [])], []) in
  match t with
  |                [] -> st0_prg
  | Int (_, Prg) :: _ -> st0_prg
  | Ext (_, Prg) :: _ -> st0_prg
  | Int (_, Ctx) :: _ -> st0_ctx
  | Ext (_, Ctx) :: _ -> st0_ctx

let reproduce_trace (st0: state) (t: trace): state =
  let step ((i, pending, finished): state) (a: action): state =
    match a with
    | Int (_, Prg) ->
       (i+1, pending, finished)
    | Int (IntCall (c', p'), Ctx) ->
       let (c, p, j, code) = List.hd pending in
       let pending' = (c', p', i, []) ::
                        (c, p, j, MCall (c', p', 0) :: code) ::
                          List.tl pending
       in
       (i+1, pending', finished)
    | Int (IntRet, Ctx) ->
       let (c, p, j, code) = List.hd pending in
       let finished' = (c, p, j, List.rev (MRet 0 :: code)) ::
                         finished in
       (i+1, List.tl pending, finished')
    | Ext (ExtCall (c', p', v), Ctx) ->
       let (c, p, j, code) = List.hd pending in
       let pending' = (c, p, j, MCall (c', p', v) :: code) ::
                        List.tl pending in
       (i+1, pending', finished)
    | Ext (ExtRet _, Prg) ->
       (i+1, pending, finished)
    | Ext (ExtRet v, Ctx) ->
       let (c, p, j, code) = List.hd pending in
       let finished' = (c, p, j, List.rev (MRet v :: code)) ::
                         finished in
       (i+1, List.tl pending, finished')
    | Ext (ExtCall (c', p', _), Prg) ->
       (i+1, (c', p', i, []) :: pending, finished)
    | Ext (Term, _) ->
       failwith "ill-formed trace"
  in
  List.fold_left step st0 t

let discriminate_action ((i, pending, finished): state)
                        (prg_a: external_action): state =
  match prg_a with
  | ExtCall (c', p', v) ->
     (i+1, pending, (c', p', i, [MCheckArg v]) :: finished)
  | ExtRet v ->
     let (c, p, j, code) = List.hd pending in
     begin
       match code with
       | MCall (c', p', v') :: code' ->
          let finished' =
            (c, p, j, List.rev (MCheckCall (c', p', v', v) :: code')) ::
              finished
          in
          (i+1, List.tl pending, finished')
       | _ ->
          failwith "ill-formed trace"
     end
  | Term ->
     (i+1, pending, finished)

let diverge_if_return ((i, pending, finished): state): state =
  let finished' =
    List.rev_append
      (List.map
         (fun (c, p, j, code) -> (c, p, j, List.rev (MDiverge :: code)))
         pending)
      finished
  in
  (i, [], finished')

let implement_distinguisher (t: trace) (prg_a: external_action):
      proc_call_descr list =
  let st0 = initial_state t in
  let st1 = reproduce_trace st0 t in
  let st2 = discriminate_action st1 prg_a in
  let final_st = diverge_if_return st2 in
  let (_, _, descrs) = final_st in
  let compare_descr (_, _, j, _) (_, _, j', _) = compare j j' in
  List.sort compare_descr descrs

(* Examples *)

let distinguisher0 =
  let c_prg = 1 in
  let t = [ Ext (ExtCall (c_prg, 0, 0), Ctx)
          ; Ext (ExtRet 1, Prg)
          ; Ext (ExtCall (c_prg, 0, 0), Ctx)
          ] in
  let prg_a = ExtRet 1 in
  implement_distinguisher t prg_a

let distinguisher1 =
  let c_ctx = 1 in
  let t = [] in
  let prg_a = ExtCall (c_ctx, 0, 1) in
  implement_distinguisher t prg_a

let distinguisher2 =
  let t = [] in
  let prg_a = Term in
  implement_distinguisher t prg_a

(* Macro instructions map to high-level expressions *)

(* High-level syntax *)
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

let translate_macro (i: component_interface) (m: macro): expr =
  let diverge: expr = ECall (i.name, i.export, EVal 0) in
  let check (e: expr): expr = EIfThenElse (e, EExit, diverge) in
  let read_arg: expr = ELoad (0, EVal 0) in
  match m with
  | MCall (c', p', v) ->
     ECall (c', p', EVal v)
  | MRet v ->
     EVal v
  | MCheckCall (c', p', v, v') ->
     check (EOp (ECall (c', p', EVal v), Eq, EVal v'))
  | MCheckArg v ->
     check (EOp (read_arg, Eq, EVal v))
  | MDiverge ->
     diverge

let translate_code (i: component_interface) (code: code) =
  let sequence (e1: expr) (e2: expr): expr = EOp (e1, Seq, e2) in
  let exprs = List.map (translate_macro i) code in
  List.fold_left sequence (List.hd exprs) (List.tl exprs)

let implement_interface (i: component_interface) (get_proc: int -> expr):
      component =
  { name = i.name;
    export = i.export;
    procs = Array.init (i.export + 1) get_proc;
    bufs = [| [|0;-1|] |] }

let extract_code (i: component_interface) p descrs =
  let read_call_id: expr = ELoad (0, EVal 1) in
  let if_call_id_else v (e1: expr) (e2: expr): expr =
    EIfThenElse (EOp (read_call_id, Eq, EVal v), e1, e2)
  in
  let diverge: expr = ECall (i.name, i.export, EVal 0) in
  let take_action: expr =
    snd (List.fold_left
           (fun (call_id, e_acc) (c',p',_,code) ->
            if c' = i.name && p' = p then
              (call_id+1,
               if_call_id_else call_id (translate_code i code) e_acc)
            else
              (call_id, e_acc))
           (0, diverge)
           descrs)
  in
  let sequence (e1: expr) (e2: expr): expr = EOp (e1, Seq, e2) in
  let incr_call_id = EStore (0, EVal 1, EOp (ELoad (0, EVal 1), Add, EVal 1)) in
  sequence incr_call_id take_action


let build_attacker (is: attacker_interface) (t: trace)
                   (prg_a: external_action): attacker =
  let descrs = implement_distinguisher t prg_a in
  List.map
    (fun i ->
     implement_interface i (fun p -> extract_code i p descrs))
    is

(* Code pretty printing *)

let pretty_print (ff: Format.formatter) (e0: expr): unit =
  let symbols = [(Eq, '='); (Seq, ';'); (Add, '+')] in
  let rec print_aux e =
    match e with
    | EVal v -> Format.fprintf ff "%d" v
    | EOp (e1, op, e2) ->
       print_aux e1;
       if op = Seq then
         Format.fprintf ff "%c @," (List.assoc op symbols)
       else
         Format.fprintf ff " %c " (List.assoc op symbols);
       print_aux e2
    | EIfThenElse (e1, e2, e3) ->
       Format.fprintf ff "if ";
       print_aux e1;
       Format.fprintf ff " then @,@[<v2>  ";
       print_aux e2;
       Format.fprintf ff "@]@,else@,@[<v2>  ";
       print_aux e3;
       Format.fprintf ff "@,@]";
    | ELoad (b, e) ->
       Format.fprintf ff "%d[" b;
       print_aux e;
       Format.fprintf ff "]"
    | EStore (b, e1, e2) ->
       Format.fprintf ff "%d[" b;
       print_aux e1;
       Format.fprintf ff "] := ";
       print_aux e2
    | ECall (c, p, e) ->
       Format.fprintf ff "%d.%d(" c p;
       print_aux e;
       Format.fprintf ff ")"
    | EExit ->
       Format.fprintf ff "exit"
  in
  Format.fprintf ff "{ @,@[<v2>  ";
  print_aux e0;
  Format.fprintf ff " @]@,}"

#install_printer pretty_print

(* Examples *)

let attacker0 =
  let is =
    [{ name = 0;
       import = [(1, 0)];
       export = 1 }]
  in
  let t = [ Ext (ExtCall (1, 0, 0), Ctx)
          ; Ext (ExtRet 1, Prg)
          ; Ext (ExtCall (1, 0, 0), Ctx)
          ] in
  let prg_a = ExtRet 1 in
  build_attacker is t prg_a

let attacker1 =
  let is =
    [{ name = 1;
       import = [];
       export = 1 }]
  in
  let t = [] in
  let prg_a = ExtCall (1, 0, 1) in
  build_attacker is t prg_a

let attacker2 =
  let is =
    [{ name = 1;
       import = [];
       export = 1 }]
  in
  let t = [] in
  let prg_a = Term in
  build_attacker is t prg_a
