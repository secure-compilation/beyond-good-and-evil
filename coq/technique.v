Require Import Coq.Lists.List.
Import ListNotations.

Require Import MutualDistrust.language.

Record product {L: language}: Type :=
  {
    compatible: list (@component L) -> list (@component L) -> Prop;
    insert: list (@component L) -> list (@component L) -> @component L
  }.

Record insertion {L: language}: Type :=
  {
    insertable: list (@component L) -> list (@component L) -> Prop;
    insert: list (@component L) -> list (@component L) -> @component L
  }.

Arguments insertable {_} _ _ _.
Arguments insert {_} _ _ _.

Section Insertion.

  Definition insertion_eq {L: language} (f g: @insertion L): Prop :=
    (forall As Rs, insertable f As Rs <-> insertable g As Rs)
    /\
    forall (As Ps Qs: list component),
      insertable f As Ps -> insertable f As Qs ->
      (beh_eq (insert f As Ps) (insert f As Qs)
       <->
       beh_eq (insert g As Ps) (insert g As Qs)).

  Definition insertion_from_map {L} (f: list (@component L) -> list (@component L)): insertion :=
    {| insertable := fun As Rs => compatible (f As Rs) /\ complete (link (f As Rs));
       insert := fun Rs => link (f As Rs) |}.

End Insertion.

Section InsertionLemmas.

  Lemma insertion_eq_refl {LP LAf: language} (f: @insertion LP LAf): insertion_eq f f.
  Proof.
    split; intros; apply iff_refl.
  Qed.

  Lemma insertion_eq_trans {LP LAf LAg LAh: language}:
    forall (f: @insertion LP LAf) (g: @insertion LP LAg) (h: @insertion LP LAh),
      insertion_eq f g -> insertion_eq g h -> insertion_eq f h.
  Proof.
    intros f g h [Hfg1 Hfg2] [Hgh1 Hgh2].
    split.
    + intros Rs; now apply (@iff_trans _ (insertable g Rs)).
    + intros Ps Qs HfPs HfQs.
      assert (insertable g Ps).
      { now apply Hfg1. }
      assert (insertable g Qs).
      { now apply Hfg1. }
      apply (@iff_trans _ (beh_eq (insert g Ps) (insert g Qs)) _).
      { now apply Hfg2. }
      { now apply Hgh2. }
  Qed.

  Lemma insertion_eq_sym {LP LAf LAg: language}:
    forall (f: @insertion LP LAf) (g: @insertion LP LAg),
      insertion_eq f g -> insertion_eq g f.
  Proof.
    intros f g [Hfg1 Hfg2].
    split.
    + intros Rs; now apply iff_sym.
    + intros Ps Qs HgPs HgQs.
      assert (insertable f Ps).
      { now apply Hfg1. }
      assert (insertable f Qs).
      { now apply Hfg1. }
      apply iff_sym.
      { now apply Hfg2. }
  Qed.

End InsertionLemmas.
