Require Import TraceSemantics.
Require Import Shape.
Require Import Compiler.

(* _____________________________________ 
               DEFINITIONS
   _____________________________________ *)

Reserved Notation "'LOW_NEQ' P '≁L' P'" (at level 40).
Inductive neq_progL : Target.program -> Target.program -> Prop :=
  | neqprogL : forall P P',
    (cprogram_terminates P /\ cprogram_diverges P')
      \/
    (cprogram_diverges P /\ cprogram_terminates P')
      ->
    (neq_progL P P')
  where "'LOW_NEQ' P '≁L' P'" := (neq_progL P P').

Reserved Notation "'HIGH_NEQ' P '≁H' P'" (at level 40).
Inductive neq_progH : Source.program -> Source.program -> Prop :=
  | neqprog : forall P P',
    (program_terminates P /\ program_diverges P')
      \/
    (program_diverges P /\ program_terminates P')
      ->
    (neq_progH P P')
  where "'HIGH_NEQ' P '≁H' P'" := (neq_progH P P').


(* _____________________________________ 
                 LEMMAS
   _____________________________________ *)

(* ------- Canonicalization ------- *)
Lemma canonicalization :
  forall t s,
  forall P, (PROGRAM_SHAPE P ∈• s) -> 
    (program_fully_defined s P) ->
    (in_Traces_p t (COMPILE_PROG P↓) s
      <-> 
     in_Traces_p (zetaC_t t) (COMPILE_PROG P↓) s).
Proof.
Admitted.

(* ------- Definability / Trace mappping algorithm ------- *)
Lemma definability :
  forall t g1 s, 
    t = zetaC_t t /\ (exists p, (LL_PROGRAM_SHAPE p ∈• s) -> 
    in_Traces_p (t++[Ext g1 ProgramOrigin]) p s)
      ->
    exists A, 
    (CONTEXT_SHAPE A ∈∘ s) /\ (context_fully_defined s A) /\
    (* 1 *)
    in_Traces_a t (COMPILE_PROG A↓) s /\
    (* 2 *)
    ((g1 <> End) -> 
    in_Traces_a (t++[Ext g1 ProgramOrigin]++[Ext End ContextOrigin]) 
      (COMPILE_PROG A↓) s) /\
    (* 3 *)
    forall g, ((zeta_gamma g) <> (zeta_gamma g1)) ->
      forall g',
      ~(in_Traces_a (t++[Ext g ProgramOrigin]++[Ext g' ContextOrigin]) 
        (COMPILE_PROG A↓) s).
Proof.
Admitted.

(* ------- Structured Full Abstraction ------- *)
Theorem structured_full_abstraction :
  forall s,
  forall P Q, 
    (PROGRAM_SHAPE P ∈• s) /\ (PROGRAM_SHAPE Q ∈• s)
      /\
    (program_fully_defined s P /\ program_fully_defined s Q)
    ->
  forall A,
    let AP := (context_application A P) in
    let AQ := (context_application A Q) in 
    (CONTEXT_SHAPE A ∈∘ s) /\ (context_fully_defined s A)
    -> HIGH_NEQ AP ≁H AQ
    -> forall a, (LL_CONTEXT_SHAPE a ∈∘ s) ->
        LOW_NEQ
        (LL_context_application a (COMPILE_PROG P↓))
          ≁L
        (LL_context_application a (COMPILE_PROG Q↓)).
Proof.
Admitted.



