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
Definition unify_option {X:Type} (default:X)
  (K : option X * option X) : X :=
  match K with
  | (Some k1', None) => k1'
  | (None, Some k2') => k2'
  | _ => default
  end.

Definition context_application (A P : Source.partial_program) :
  Source.program :=
  map (unify_option (0,0,[],0,0,[])) (combine A P).


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

Reserved Notation "'LL_CONTEXT_SHAPE' A ∈∘ s" (at level 40).
Inductive ll_context_has_shape : 
  Target.program -> shape -> Prop :=
  | SH_LLcontext : forall Is_a mem E Is comps_id,
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
    let not_in_compsid := 
      fun (C:option component_id) =>
        negb (existsb (f C) comps_id)
    in
    (forall i, (In i Is_a) -> 
      ((nth (get_name i) Is (0,0,[])) = i)) ->
    (dom_entry_points E = dom_global_memory mem) ->
    (dom_global_memory mem = 
      (dom2partial (compsInterface Is_a))) ->
    (dom2partial (compsInterface Is_a) = 
      filter not_in_compsid (dom2partial (compsInterface Is))) ->
    LL_CONTEXT_SHAPE (Is_a, mem, E) ∈∘ (Is, comps_id)
  where "'LL_CONTEXT_SHAPE' A ∈∘ s" := 
  (ll_context_has_shape A s).

(* ------- Context application ------- *)

Definition LL_context_application (A P:Target.program) :
  Target.program :=
  match A with
  | (Is_a, mem_a, E_a) =>
    match P with
    | (Is_p, mem_p, E_p) =>
      (Is_a ++ Is_p,
       mem_a ++ mem_p,
       E_a ++ E_p)
    end
  end.


(* _____________________________________ 
            FULL DEFINEDNESS
   _____________________________________ *)

Inductive program_fully_defined : partial_program -> Prop :=
  | FD_program : forall P (PC:Source.program) C s sh d K e,
    (PROGRAM_SHAPE P ∈• sh) ->
  ~(exists A, (CONTEXT_SHAPE A ∈∘ sh) ->
    let PC := (context_application A P) in
    (procbodies PC) ⊢ (initial_cfg_of PC) ⇒* (C,s,d,K,e) ->
    undefined_cfg (procbodies PC) (C,s,d,K,e) ->
    In C (compsComponent PC)) ->
    program_fully_defined P.

Inductive context_fully_defined : partial_program -> Prop :=
  | FD_context : forall A (PC:Source.program) C s sh d K e,
    (CONTEXT_SHAPE A ∈∘ sh) ->
  ~(exists P, (PROGRAM_SHAPE P ∈• sh) ->
    let PC := (context_application A P) in
    (procbodies PC) ⊢ (initial_cfg_of PC) ⇒* (C,s,d,K,e) ->
    undefined_cfg (procbodies PC) (C,s,d,K,e) ->
    In C (compsComponent PC)) ->
    context_fully_defined A.




