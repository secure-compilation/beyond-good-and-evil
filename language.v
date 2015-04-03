(** We define what we mean by a language in this formalization, by
providing a datatype for languages. We also introduce some
notations. *)

Require Import Coq.Relations.Relations.

(* This definition is currently too restrictive. *)

Record language: Type := MkLanguage {
  program: Type;
  context: Type;
  value: Type;
  in_context: context -> program -> program;
  eval: program -> option value;
  value_eq: relation value;
  value_eq_is_an_equivalence: equivalence value value_eq
}.

Arguments in_context [_] _ _.
Arguments eval [_] _.
Arguments value_eq [_] _ _.

Notation "c <| p |>" := (in_context c p) (at level 20): language_scope.

Notation "# p" := (eval p) (at level 25): language_scope.
