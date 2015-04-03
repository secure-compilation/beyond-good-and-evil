(** We give the skeleton of the work of Patrignani (with a lot of
holes). *)

Require Import Ssreflect.ssreflect.
Require Import Ssreflect.ssrbool.
Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relations.
Require Import samerelation.
Require Import language.
Require Import contextualequivalence.
Require Import fullabstraction.

Local Arguments same_relation [_] _ _.

Local Open Scope language_scope.

(** Define the source language. *)

Section JPlusE.

  Lemma jpluse: language.
  Proof.
    admit.
  Qed.

End JPlusE.


(** Define the target language, and trace equivalence. *)

Section APlusI.

  Definition aplusi: language.
  Proof.
    admit.
  Qed.

  Lemma trace_equivalence_aplusi: relation (program aplusi).
  Proof.
    admit.
  Qed.

End APlusI.

Infix "<T>" := trace_equivalence_aplusi (at level 60).


(** Define the compilation scheme. *)

Section Compilation.

  Lemma compile: program jpluse -> program aplusi.
  Proof.
    admit.
  Qed.

End Compilation.


(** Show full abstraction for the compilation scheme. *)

Section FullAbstractionResult.

  (** This is the main result of PatrignaniASJCP15. *)
  Theorem full_abstraction_through_trace_equivalence:
    same_relation (fun p q => p <||> q) (fun p q => compile p <T> compile q).
  Proof.
    admit.
  Qed.

  (** This is the main result of PatrignaniC15. *)
  Theorem trace_equivalence_coincides_with_contextual_equivalence_on_compiled_programs:
    same_relation (fun p q => compile p <T> compile q) (fun p q => compile p <||> compile q).
  Proof.
    admit.
  Qed.

  (** Full abstraction is a corollary of these two results. *)
  Theorem full_abstraction_of_compilation_scheme: fully_abstract compile.
  Proof.
    pose rmiddle p q := compile p <T> compile q.
    by apply: (same_relation_transitivity _ rmiddle _); [
      apply: full_abstraction_through_trace_equivalence
      | apply: trace_equivalence_coincides_with_contextual_equivalence_on_compiled_programs
    ].
  Qed.

End FullAbstractionResult.
