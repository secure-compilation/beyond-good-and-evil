(** We define full abstraction: a compilation scheme is fully abstract
if contextual equivalence on source programs coincides with contextual
equivalence on compiled source programs.

We first give a Coq-friendly definition, then we show as a sanity
check that it is equivalent to another, more intuitive definition
which is the one used in PatrignaniASJCP15.

We prove properties about full abstraction, e.g. that it is
preserved by composition, that could be used to build a category with
languages as objects and fully abstract compilation schemes as
morphisms.

We introduce a relation [fully_abstracts] between languages defined as
such: T fully abstracts S, noted [fully_abstracts S T] when there
exists a fully abstract compilation. Then, we prove that it is a
preorder. *)

Require Import Ssreflect.ssreflect.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics. (* composition *)
Require Import Coq.Relations.Relations.
Require Import samerelation.
Require Import language.
Require Import contextualequivalence.

Local Arguments same_relation [_] _ _.

Local Open Scope language_scope.

(** Let's define full abstraction. *)

Section Definitions.

  Variables (S T: language).


  Definition fully_abstract (c: program S -> program T): Prop :=
    same_relation (fun p q => p <||> q) (fun p q => c p <||> c q).

  Definition fully_abstracts: Prop :=
    exists (c: program S -> program T), fully_abstract c.

End Definitions.

Arguments fully_abstract [S] [T] _.


(** Let's prove that our definition is equivalent to an intuitive
one. *)

Section IsIntuitive.

  Variables (S T: language).


  Definition intuitive_full_abst (c: program S -> program T): Prop :=
    forall (p q: program S), (p <||> q) <-> (c p <||> c q).

  Theorem full_abstraction_is_intuitive:
    forall (c: program S -> program T),
    fully_abstract c <-> intuitive_full_abst c.
  Proof.
    by move=> c; apply: same_relation_is_propositional_equivalence.
  Qed.

End IsIntuitive.


(** Let's prove that identity is a fully abstract compilation scheme
and that composition preserves full abstraction. *)

Section Properties.

  Theorem id_scheme_is_fully_abstract:
    forall L: language, @fully_abstract L L (fun p => p).
  Proof.
    by move=> L; apply: conj.
  Qed.

  Theorem full_abstraction_is_preserved_by_composition:
    forall {S I T: language}
           {c1 : program S -> program I}
           {c2 : program I -> program T},
    fully_abstract c1 ->
    fully_abstract c2 ->
    fully_abstract (compose c2 c1).
  Proof.
    move=> S I T c1 c2 hfullabstc1 [hfullabstc2r hfullabstc2l].
    pose rmiddle p q := c1 p <||> c1 q.
    by apply: (same_relation_transitivity _ rmiddle _); [
      apply: hfullabstc1
      | apply: conj; move=> p q; [
          apply: hfullabstc2r
          | apply: hfullabstc2l
        ]
    ].
  Qed.

  Theorem fully_abstracts_is_a_preorder:
    preorder language fully_abstracts.
  Proof.
    by apply: Build_preorder; [
      (* reflexivity *)
      move => L; exists (fun p => p); apply: id_scheme_is_fully_abstract
      | (* transitivity *)
        move => S I T [c1 hfullabstc1] [c2 hfullabstc2];
        exists (compose c2 c1);
        apply: full_abstraction_is_preserved_by_composition
    ].
   Qed.

End Properties.


(** Let's start building a category out of these properties. *)

Section Category.

  Definition obj := language.

  Definition hom (A B: obj) :=
    {c: program A -> program B | fully_abstract c}.

  Definition hom_eq {A B: obj} (f g: hom A B) :=
    proj1_sig f = proj1_sig g.

  Program Definition id_hom {A: obj}: hom A A := fun p => p.
  Next Obligation.
    by apply: id_scheme_is_fully_abstract.
  Qed.

  Program Definition hom_compose {A B C: obj}:
    hom B C -> hom A B -> hom A C
  :=
    compose.
  Next Obligation.
    by apply: full_abstraction_is_preserved_by_composition;
       apply: proj2_sig.
  Qed.

  Theorem hom_compose_is_associative {A B C D: obj}:
    forall (f: hom A B) (g: hom B C) (h: hom C D),
      hom_eq (hom_compose (hom_compose h g) f)
             (hom_compose h (hom_compose g f)).
  Proof.
    by move => f g h; compute.
  Qed.

  Theorem id_is_left_neutral {A B: obj}:
    forall f: hom A B, hom_eq (hom_compose id_hom f) f.
  Proof.
    by move=> f; compute.
  Qed.

  Theorem id_is_right_neutral {A B: obj}:
    forall f: hom A B, hom_eq (hom_compose f id_hom) f.
  Proof.
    by move=> f; compute.
  Qed.

End Category.
