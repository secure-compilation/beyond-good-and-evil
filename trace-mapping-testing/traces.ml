(* Trace syntax *)
type origin = Ctx | Prg
type internal_action =
  | IntCall of int * int (* C.P(/) *)
  | IntRet               (* Ret / *)
  | IntTau
type external_action =
  | ExtCall of int * int * int (* C.P(reg) with r≠r_com ⇒ reg[r]=0 *)
  | ExtRet of int              (* Ret reg  with r≠r_com ⇒ reg[r]=0 *)
  | Term                       (* ✓ *)
type alpha =
  | Int of internal_action * origin (* Iα *)
  | Ext of external_action * origin (* Eα *)
type trace = alpha list

let dual t =
  List.map
    (fun alpha ->
     match alpha with
     | Int (ia, Prg) -> Int (ia, Ctx)
     | Int (ia, Ctx) -> Int (ia, Prg)
     | Ext (ea, Prg) -> Ext (ea, Ctx)
     | Ext (ea, Ctx) -> Ext (ea, Prg))
    t
