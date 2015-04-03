(** We prove properties about same_relation that do not seem to be
stated in the standard library:
  * transitivity ;
  * a characterization through propositional equivalence. *)

Require Import Ssreflect.ssreflect.
Require Import Coq.Relations.Relations.

Local Arguments inclusion [_] _ _.
Local Arguments same_relation [_] _ _.


(** Let's prove that same_relation is transitive. *)

Section Transitivity.

  Lemma inclusion_transitivity:
    forall {A: Type} (r1 r2 r3: relation A),
      inclusion r1 r2 -> inclusion r2 r3 -> inclusion r1 r3.
  Proof.
    move=> A r1 r2 r3 hincr1r2 hincr2r3 x yy hr1xy.
    by apply: hincr2r3; apply: hincr1r2.
  Qed.

  Theorem same_relation_transitivity:
    forall {A: Type} (r1 r2 r3: relation A),
      same_relation r1 r2 ->
      same_relation r2 r3 ->
      same_relation r1 r3.
  Proof.
    move=> A r1 r2 r3 [hincr1r2 hincr2r1] [hincr2r3 hincr3r2].
    by apply: conj; apply: (inclusion_transitivity _ r2 _).
  Qed.

End Transitivity.


(** Let's prove that same_relation is characterized by
propositional equivalence. *)

Section Characterization.

  Theorem same_relation_is_propositional_equivalence :
    forall {A: Type} (r1 r2: relation A),
      same_relation r1 r2 <-> (forall (x y: A), r1 x y <-> r2 x y).
    move=> A r1 r2.
    apply: conj.
      by move=> [hincr1r2 hincr2r1] x y; apply: conj; [
        apply: hincr1r2 | apply: hincr2r1
      ].
    by move=> hequivr1r2; apply: conj; move=> x y;
       move: (hequivr1r2 x y) => [hr1ir2xy hr2ir1xy].
  Qed.

End Characterization.
