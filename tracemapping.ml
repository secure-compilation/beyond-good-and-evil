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

let reproduce_trace t =
  let step (i, current, pending, past) action =
    match action with
    | Int (_, Prg) ->
       (i+1, current, pending, past)
    | Int (IntCall (c', p'), Ctx) ->
       let (c, p, j, code) = current in
       (i+1, (c', p', i, []), (c, p, j, ICall (c', p', 0) :: code) :: pending, past)
    | Int (IntRet, Ctx) ->
       let (c, p, j, code) = current in
       (i+1, List.hd pending, List.tl pending, (c, p, j, List.rev (IRet 0 :: code)) :: past)
    | Ext (ExtCall (c', p', v), Ctx) ->
       let (c, p, j, code) = current in
       (i+1, (c, p, j, ICall (c', p', v) :: code), pending, past)
    | Ext (ExtRet _, Prg) ->
       (i+1, current, pending, past)
    | Ext (ExtRet v, Ctx) ->
       let (c, p, j, code) = current in
       (i+1, List.hd pending, List.tl pending, (c, p, j, List.rev (IRet v :: code)) :: past)
    | Ext (ExtCall (c', p', v), Prg) ->
       (i+1, current, pending, past)
    | Ext (Term, _) ->
       failwith "ill-formed trace"
  in
  let st0 = (0, (c_main, p_main, -1, []), [], []) in
  List.fold_left step st0 t

let discriminate_action (i, current, pending, past) ext_prg_action =
  match ext_prg_action with
  | ExtCall (c', p', v) ->
     (current :: pending, (c', p', i, [ICheckArg v]) :: past)
  | ExtRet v ->
     let (c, p, j, code) = current in
     begin
       match code with
       | ICall (c', p', v') :: code' ->
	  (pending, (c, p, j, ICheckCall (c', p', v', v) :: code') :: past)
       | _ ->
	  failwith "ill-formed trace"
     end
  | Term ->
     (current :: pending, past)

let close_pending_calls (pending, past) =
  (List.rev (List.map
	       (fun (c, p, j, code) ->
		(c, p, j, List.rev (IDiverge :: code)))
	       pending))
  @ past
