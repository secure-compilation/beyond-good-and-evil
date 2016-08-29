open Traces
open Semantics

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
              (begin if c' = i.name then call_id + 1 else call_id end, e_acc))
           (0, diverge)
           descrs)
  in
  let sequence (e1: expr) (e2: expr): expr = EOp (e1, Seq, e2) in
  let incr_call_id = EStore (0, EVal 1, EOp (ELoad (0, EVal 1), Add, EVal 1)) in
  sequence incr_call_id take_action
