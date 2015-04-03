(** We define contextual equivalence: two programs are contextually
equivalent if, when both placed in the same arbitrary context, either
evaluation is undefined for both, or both evaluate to the same value.

We first define a Coq-friendly definition of contextual equivalence,
that will be used in the rest of the formalization, and show that it
is indeed an equivalence relation. Then, before moving to the next
sections, we show as a sanity check that it is equivalent to another,
more intuitive definition of contextual equivalence, which is closer
to Plotkin77. *)

Require Import Ssreflect.ssreflect.
Require Import Coq.Program.Equality. (* dependent destruction *)
Require Import Coq.Relations.Relations.
Require Import language.

Local Open Scope language_scope.

(** Let's define contextual equivalence. *)

Section Definitions.

  Variable L: language.


  Inductive option_value_eq : relation (option (value L)) :=
    | oveq_none : option_value_eq None None
    | oveq_some (v1 v2: value L):
        value_eq v1 v2 -> option_value_eq (Some v1) (Some v2)
  .

  (* This definition may be too simple, e.g. in JeffreyR05 contextual
 equivalence is defined in a much more complicated way. *)
  Definition contextual_equivalence (p q: program L) :=
    forall (c: context L), option_value_eq (#c<|p|>) (#c<|q|>).

End Definitions.

Arguments contextual_equivalence [L] _ _.

Infix "<||>" := contextual_equivalence (at level 60): language_scope.


(** Let's prove that we do have an equivalence relation. *)

Section IsAnEquivalence.

  Variable L: language.


  Lemma option_value_eq_is_an_equivalence:
    equivalence (option (value L)) (option_value_eq L).
  Proof.
    move: (value_eq_is_an_equivalence L) => [hrefl htrans hsym].
    apply: Build_equivalence.
        by move=> [v|]; [apply: oveq_some | apply: oveq_none].
      by move=> ov1 [v2|] ov3 heqov1ov2 heqov2ov3;
         dependent destruction heqov1ov2;
         dependent destruction heqov2ov3; [
           apply: oveq_some; apply: (htrans _ v2 _)
           | apply: oveq_none
         ].
    by move=> [v1|] ov2 heqov1ov2; dependent destruction heqov1ov2; [
      apply: oveq_some; apply: hsym
      | apply: oveq_none
    ].
  Qed.

  Theorem contextual_equivalence_is_an_equivalence:
    equivalence (program L) (@contextual_equivalence L).
  Proof.
    move: option_value_eq_is_an_equivalence => [] hrefl htrans hsym.
    apply: Build_equivalence.
        by move=> p c; apply: hrefl.
      by move=> p q r hpq hqr c; apply: (htrans _ (#c<|q|>) _).
    by move=> p q hpq c; apply: hsym.
  Qed.

End IsAnEquivalence.


(** Let's prove that our definition is equivalent to an intuitive one. *)

Section IsIntuitive.

  Variable L: language.


  Definition intuitive_contextual_equivalence p q :=
    forall (c: context L),
      match #c<|p|> with
        | None    => #c<|q|> = None
        | Some v1 => exists v2, #c<|q|> = Some v2 /\ value_eq v1 v2
      end.

  Lemma option_value_eq_is_intuitive:
    forall (ov1 ov2: option (value L)),
      option_value_eq L ov1 ov2 <->
      match ov1 with
        | None => ov2 = None
        | Some v1 => exists v2, ov2 = Some v2 /\ value_eq v1 v2
      end.
  Proof.
    move=> ov1 ov2.
    apply: conj.
      by move: ov1 => [v1|] heqov1ov2;
         dependent destruction heqov1ov2;
         [exists v2|].
    move: ov1 => [v1|].
      by move=> [v2 [hlinkv2ov2 heqv1v2]];
         rewrite hlinkv2ov2;
         apply: oveq_some.
    by move=> heqov2none;
       rewrite heqov2none;
       apply: oveq_none.
  Qed.

  Theorem contextual_equivalence_is_intuitive:
    forall (p q: program L),
    p <||> q <-> intuitive_contextual_equivalence p q.
  Proof.
    pose hint c p q :=
      option_value_eq_is_intuitive (#c<|p|>) (#c<|q|>).
    by move=> p q; apply: conj; move=> heqpq c;
       move: (hint c p q) => [hright hleft]; [
         apply: hright | apply: hleft
       ]; apply: heqpq.
  Qed.

End IsIntuitive.
