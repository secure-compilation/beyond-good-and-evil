type origin = Ctx | Prg
type internal_action = IntCall of int * int | IntRet
type external_action = ExtCall of int * int * int | ExtRet of int | Term
type action = Int of internal_action * origin | Ext of external_action * origin
type trace = action list

type instr = ICall of int * int * int | IRet of int | ICheckCall of int * int * int * int | ICheckArg of int | IDiverge
type code = instr list
type proc_call_descr = int * int * int * code

let c_main = 0
let p_main = 0

let initial_state t ext_prg_action =
  let st0_prg = (0, [], []) in
  let st0_ctx = (0, [(c_main, p_main, -1, [])], []) in
  match t with
  |                [] -> st0_prg
  | Int (_, Prg) :: _ -> st0_prg
  | Ext (_, Prg) :: _ -> st0_prg
  | Int (_, Ctx) :: _ -> st0_ctx
  | Ext (_, Ctx) :: _ -> st0_ctx

let reproduce_trace st0 t =
  let step (i, pending, finished) action =
    match action with
    | Int (_, Prg) ->
       (i+1, pending, finished)
    | Int (IntCall (c', p'), Ctx) ->
       let (c, p, j, code) = List.hd pending in
       let pending' = (c', p', i, []) ::
			(c, p, j, ICall (c', p', 0) :: code) ::
			  List.tl pending in
       (i+1, pending', finished)
    | Int (IntRet, Ctx) ->
       let (c, p, j, code) = List.hd pending in
       let finished' = (c, p, j, List.rev (IRet 0 :: code)) :: finished in
       (i+1, List.tl pending, finished')
    | Ext (ExtCall (c', p', v), Ctx) ->
       let (c, p, j, code) = List.hd pending in
       let pending' = (c, p, j, ICall (c', p', v) :: code) :: List.tl pending in
       (i+1, pending', finished)
    | Ext (ExtRet _, Prg) ->
       (i+1, pending, finished)
    | Ext (ExtRet v, Ctx) ->
       let (c, p, j, code) = List.hd pending in
       let finished' = (c, p, j, List.rev (IRet v :: code)) :: finished in
       (i+1, List.tl pending, finished')
    | Ext (ExtCall (c', p', _), Prg) ->
       (i+1, (c', p', i, []) :: pending, finished)
    | Ext (Term, _) ->
       failwith "ill-formed trace"
  in
  List.fold_left step st0 t

let discriminate_action (i, pending, finished) ext_prg_action =
  match ext_prg_action with
  | ExtCall (c', p', v) ->
     (pending, (c', p', i, [ICheckArg v]) :: finished)
  | ExtRet v ->
     let (c, p, j, code) = List.hd pending in
     begin
       match code with
       | ICall (c', p', v') :: code' ->
	  let finished' = (c, p, j, List.rev (ICheckCall (c', p', v', v) :: code')) ::
			    finished in
	  (List.tl pending, finished')
       | _ ->
	  failwith "ill-formed trace"
     end
  | Term ->
     (pending, finished)

let finish_pending (pending, finished) =
  List.rev_append
    (List.map
       (fun (c, p, j, code) -> (c, p, j, List.rev (IDiverge :: code)))
       pending)
     finished

let implement_distinguisher t ext_prg_action =
  let st0 = initial_state t ext_prg_action in
  let st = reproduce_trace st0 t in
  let pending_finished = discriminate_action st ext_prg_action in
  let impls = finish_pending pending_finished in
  let comp (c, p, j, _) (c', p', j', _) = compare (c, p, j) (c', p', j') in
  List.sort comp impls

let distinguisher0 =
  let c_prg = 1 in
  let t = [ Ext (ExtCall (c_prg, 0, 0), Ctx)
	  ; Ext (ExtRet 1, Prg)
	  ; Ext (ExtCall (c_prg, 0, 0), Ctx)
	  ] in
  let ext_prg_action = ExtRet 1 in
  implement_distinguisher t ext_prg_action

let distinguisher1 =
  let c_ctx = 1 in
  let t = [] in
  let ext_prg_action = ExtCall (c_ctx, 0, 1) in
  implement_distinguisher t ext_prg_action

let distinguisher2 =
  let t = [] in
  let ext_prg_action = Term in
  implement_distinguisher t ext_prg_action
