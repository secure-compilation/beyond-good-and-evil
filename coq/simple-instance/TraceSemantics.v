Require Import Target.

(* _____________________________________ 
                  SYNTAX
   _____________________________________ *)

Inductive origin : Type :=
  | ContextOrigin : origin
  | ProgramOrigin : origin.

Inductive external_action : Type :=
  | ExtCall : component_id -> procedure_id -> register -> 
    external_action
  | ExtRet : register -> external_action
  | End : external_action.

Inductive internal_action : Type :=
  | IntTau : internal_action
  | IntCall : component_id -> procedure_id ->
    internal_action
  | IntRet : internal_action.

Inductive action : Type :=
  | Ext : external_action -> origin -> action
  | Int : internal_action -> origin -> action.

(*Definition dual (t:label) :=
  let f :=
    (fun alpha =>
     match alpha with
     | Int ia ProgramOrigin => Int ia ContextOrigin
     | Int ia ContextOrigin => Int ia ProgramOrigin
     | Ext ea ProgramOrigin => Ext ea ContextOrigin
     | Ext ea ContextOrigin => Ext ea ProgramOrigin
     end) in
  map f t.
*)






