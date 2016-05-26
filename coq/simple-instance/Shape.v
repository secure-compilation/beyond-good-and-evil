Require Import Target.

(* _____________________________________ 
               DEFINITIONS
   _____________________________________ *)

Definition shape : Type :=
  (program_interfaces * list component_id).

Definition get_interfacesS (s:shape) : program_interfaces :=
  match s with
  | (Is, _) => Is
  end.

Definition get_component_idS (s:shape) : list component_id :=
  match s with
  | (_, comps_id) => comps_id
  end. 


(* _____________________________________ 
              WELL-FORMEDNESS
   _____________________________________ *)

Inductive wellformed_shape : shape -> Prop :=
  | WF_shape : forall s,
    let Is := get_interfacesS s in
    let comps_id := get_component_idS s in
    wellformed_interfaces Is ->
    incl comps_id (dom_interfaces Is) ->
    wellformed_shape s.

(* _____________________________________ 
                HAS SHAPE
   _____________________________________ *)

Reserved Notation "'PROGRAM_SHAPE' P ∈• s" (at level 40).
Inductive program_has_shape (P:Source.program) :
  shape -> Prop :=
  | SH_program : forall s,
    let Is := get_interfacesS s in
    let comps_id := get_component_idS s in 
    wellformed_partial_program Is P ->
    (compsProgram P = comps_id) ->
    PROGRAM_SHAPE P ∈• s
  where "'PROGRAM_SHAPE' P ∈• s" := (program_has_shape P s).

Reserved Notation "'CONTEXT_SHAPE' P ∈∘ s" (at level 40).
Inductive context_has_shape (P:Source.program) :
  shape -> Prop :=
  | SH_context : forall s,
    let Is := get_interfacesS s in
    let comps_id := get_component_idS s in
    let not_in_compsId := 
      fun (C:component_id) =>
        negb (existsb (fun x => x =? C) comps_id)
    in
    wellformed_partial_program Is P ->
    dom_program P = 
      (filter not_in_compsId (compsInterface Is)) ->
    CONTEXT_SHAPE P ∈∘ s
  where "'CONTEXT_SHAPE' P ∈∘ s" := (context_has_shape P s). 
