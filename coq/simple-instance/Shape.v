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
             SOURCE LANGUAGE
   _____________________________________ *)

(* ------- Well-formedness ------- *)
Inductive wellformed_shape : shape -> Prop :=
  | WF_shape : forall s,
    let Is := get_interfacesS s in
    let comps_id := get_component_idS s in
    wellformed_interfaces Is ->
    incl comps_id (dom2partial (dom_interfaces Is)) ->
    wellformed_shape s.


(* ------- Has shape ------- *)
Reserved Notation "'PROGRAM_SHAPE' P ∈• s" (at level 40).
Inductive program_has_shape :
  Source.partial_program -> shape -> Prop :=
  | SH_program : forall P Is comps_id,
    wellformed_partial_program_alt Is P ->
    (compsPartialProgram P = comps_id) ->
    PROGRAM_SHAPE P ∈• (Is, comps_id)
  where "'PROGRAM_SHAPE' P ∈• s" := (program_has_shape P s).

Reserved Notation "'CONTEXT_SHAPE' P ∈∘ s" (at level 40).
Inductive context_has_shape :
  Source.partial_program -> shape -> Prop :=
  | SH_context : forall P Is comps_id,
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
    CONTEXT_SHAPE P ∈∘ (Is, comps_id)
  where "'CONTEXT_SHAPE' P ∈∘ s" := (context_has_shape P s).

(* ------- Context application ------- *)
Definition unify_components 
  (K : option component * option component) : component :=
  match K with
  | (Some k1', None) => k1'
  | (None, Some k2') => k2'
  | _ => (0,0,[],0,0,[])
  end.

Definition context_application (A P : Source.partial_program) :
  Source.program :=
  map unify_components (combine A P).


(* _____________________________________ 
                  PROOFS
   _____________________________________ *)

Theorem context_application_preserves_wellformedness :
  forall A P s, 
  (wellformed_shape s) /\ 
  (CONTEXT_SHAPE A ∈∘ s) /\ (PROGRAM_SHAPE P ∈• s) ->
  wellformed_whole_program (context_application A P).
Proof.
Admitted.


(* _____________________________________ 
             TARGET LANGUAGE
   _____________________________________ *)

(* ------- Has shape ------- *)

Reserved Notation "'LL_PROGRAM_SHAPE' P ∈• s" (at level 40).
Inductive ll_program_has_shape : 
  Target.program -> shape -> Prop :=
  | SH_LLprogram : forall Is_p mem E Is comps_id,
    (forall i, (In i Is_p) -> 
      ((nth (get_name i) Is (0,0,[])) = i)) ->
    (dom_entry_points E = dom_global_memory mem) ->
    (dom_global_memory mem = 
      (dom2partial (compsInterface Is_p))) ->
    (dom2partial (compsInterface Is_p) = comps_id) ->
    LL_PROGRAM_SHAPE (Is_p, mem, E) ∈• (Is, comps_id)
  where "'LL_PROGRAM_SHAPE' P ∈• s" := 
  (ll_program_has_shape P s).

(* TODO *)

