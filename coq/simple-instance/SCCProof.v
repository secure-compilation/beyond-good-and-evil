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



