Require Import Source.
Require Import Target.

(* _____________________________________ 
               DEFINITIONS
   _____________________________________ *)

Definition shape : Type :=
  (program_interfaces * list (option component_id)).

Definition get_interfacesS (s:shape) : program_interfaces :=
  match s with
  | (Is, _) => Is
  end.

Definition get_component_idS (s:shape) : 
  list (option component_id) :=
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
    incl comps_id (dom2partial (dom_interfaces Is)) ->
    wellformed_shape s.

(* _____________________________________ 
                HAS SHAPE
   _____________________________________ *)

Reserved Notation "'PROGRAM_SHAPE' P ∈• s" (at level 40).
Inductive program_has_shape (P:Source.partial_program) :
  shape -> Prop :=
  | SH_program : forall s,
    let Is := get_interfacesS s in
    let comps_id := get_component_idS s in 
    wellformed_partial_program_alt Is P ->
    (compsPartialProgram P = comps_id) ->
    PROGRAM_SHAPE P ∈• s
  where "'PROGRAM_SHAPE' P ∈• s" := (program_has_shape P s).

Reserved Notation "'CONTEXT_SHAPE' P ∈∘ s" (at level 40).
Inductive context_has_shape (P:Source.partial_program) :
  shape -> Prop :=
  | SH_context : forall s,
    let Is := get_interfacesS s in
    let comps_id := get_component_idS s in
    let f C x :=
      match C with
      | Some C' =>
        match x with
        | Some x' => C' =? x'
        | None => false
        end
      | None => false
      end
    in
    let not_in_compsId := 
      fun (C:option component_id) =>
        negb (existsb (f C) comps_id)
    in
    wellformed_partial_program_alt Is P ->
    dom_partial_program P = 
      (filter not_in_compsId (dom2partial (compsInterface Is))) ->
    CONTEXT_SHAPE P ∈∘ s
  where "'CONTEXT_SHAPE' P ∈∘ s" := (context_has_shape P s). 
