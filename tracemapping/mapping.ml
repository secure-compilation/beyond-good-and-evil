(* Trace mapping algorithm *)

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

(* Note: The trace input to the algorithm is not t itself, but a trace
         with internal actions T that erases to t. More details are
         provided in the proof intuition section for the definability
         lemma. *)

open Traces
open Semantics
open Macros

(* First step: Map trace and action to pseudo-code *)

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
  let step ((i, pending, finished): state) (a: alpha): state =
    match a with
    | Int (_, Prg)
    | Int (IntTau, Ctx) ->
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

let build_attacker (is: attacker_interface) (t: trace)
                   (prg_a: external_action): attacker =
  let descrs = implement_distinguisher t prg_a in
  List.map
    (fun i ->
     implement_interface i (fun p -> extract_code i p descrs))
    is
