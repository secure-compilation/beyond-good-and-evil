Require Import Coq.Lists.List.
Import ListNotations.

Record language: Type :=
  {
    component: Set;
    empty: component;
    link2: component -> component -> component;

    compatible2: component -> component -> Prop;
    complete: component -> Prop;
    beh_eq: component -> component -> Prop;

    compatible2_narrow:
      forall P Q R,
        compatible2 Q R ->
        compatible2 P (link2 Q R) -> compatible2 P Q;
    complete_widen2:
      forall (A P: component),
        compatible2 A P ->
        complete P ->
        complete (link2 A P);

    compatible2_dec: forall (P Q: component), {compatible2 P Q} + {~ compatible2 P Q};
    complete_dec: forall (P: component), {complete P} + {~ complete P};

    beh_eq_refl: forall (P: component), complete P -> beh_eq P P;
    beh_eq_sym: forall (P Q: component),
                  complete P -> complete Q ->
                  beh_eq P Q ->
                  beh_eq Q P;
    beh_eq_trans: forall (P Q R: component),
                    complete P -> complete Q -> complete R ->
                    beh_eq P Q -> beh_eq Q R ->
                    beh_eq P R
  }.

Arguments component {_}.
Arguments empty {_}.
Arguments link2 {_} _ _.

Arguments compatible2 {_} _ _.
Arguments complete {_} _.
Arguments beh_eq {_} _ _.

Arguments compatible2_narrow {_} _ _ _ _ _.
Arguments complete_widen2 {_} _ _ _ _.

Arguments compatible2_dec {_} _ _.
Arguments complete_dec {_} _.

Arguments beh_eq_refl {_} _ _.
Arguments beh_eq_sym {_} _ _ _ _ _.
Arguments beh_eq_trans {_} _ _ _ _ _ _ _ _.

Section Hyps.

  Variable (L: language).

  Record neutr_left_hyp: Prop :=
    {
      neutr_left_compatible2:
        forall (P: @component L),
          compatible2 empty P;
      neutr_left_complete_link2:
        forall (P: @component L),
          complete P ->
          complete (link2 empty P);
      neutr_left_beh_eq_link2:
        forall (P: @component L),
          complete P ->
          beh_eq P (link2 empty P)
    }.

  Record assoc_hyp: Prop :=
    {
      assoc_neutr_left: neutr_left_hyp;
      assoc_compatible2:
        forall (P Q R: @component L),
          compatible2 P Q ->
          compatible2 Q R ->
          compatible2 P (link2 Q R) ->
          compatible2 (link2 P Q) R;
      assoc_complete_link2:
        forall (A P Q R: @component L),
          compatible2 Q R ->
          compatible2 P (link2 Q R) ->
          compatible2 A (link2 P (link2 Q R)) ->
          complete (link2 A (link2 P (link2 Q R))) ->
          complete (link2 A (link2 (link2 P Q) R));
      assoc_beh_eq_link2:
        forall (A P Q R: @component L),
          compatible2 Q R ->
          compatible2 P (link2 Q R) ->
          compatible2 A (link2 P (link2 Q R)) ->
          complete (link2 A (link2 P (link2 Q R))) ->
          beh_eq (link2 A (link2 P (link2 Q R))) (link2 A (link2 (link2 P Q) R))
    }.

  Record comm_hyp: Prop :=
    {
      comm_assoc: assoc_hyp;
      comm_compatible2_sym:
        forall (P Q: @component L),
          compatible2 P Q ->
          compatible2 Q P;
      comm_compatible2:
        forall (A P Q: @component L),
          compatible2 P Q ->
          compatible2 A (link2 P Q) ->
          compatible2 A (link2 Q P);
      comm_complete_link2:
        forall (A P Q: @component L),
          compatible2 A (link2 P Q) ->
          complete (link2 A (link2 P Q)) ->
          complete (link2 A (link2 Q P));
      comm_beh_eq_link2:
        forall (A P Q: @component L),
          compatible2 P Q ->
          compatible2 A (link2 P Q) ->
          complete (link2 A (link2 P Q)) ->
          beh_eq (link2 A (link2 P Q)) (link2 A (link2 Q P))
    }.

End Hyps.

Arguments neutr_left_compatible2 {_} _ _.
Arguments neutr_left_complete_link2 {_} _ _ _.
Arguments neutr_left_beh_eq_link2 {_} _ _ _.

Arguments assoc_neutr_left {_} _.
Arguments assoc_compatible2 {_} _ _ _ _ _ _ _.
Arguments assoc_complete_link2 {_} _ _ _ _ _ _ _ _ _.
Arguments assoc_beh_eq_link2 {_} _ _ _ _ _ _ _ _ _.

Arguments comm_assoc {_} _.
Arguments comm_compatible2_sym {_} _ _ _ _.
Arguments comm_compatible2 {_} _ _ _ _ _ _.
Arguments comm_complete_link2 {_} _ _ _ _ _ _.
Arguments comm_beh_eq_link2 {_} _ _ _ _ _ _ _.

Section Nary.

  Variable (L: language).

  Fixpoint link (Ps: list (@component L)) :=
    match Ps with
      | [] => empty
      | [P] => P
      | P :: Ps' => link2 P (link Ps')
    end.

  Fixpoint compatible (Ps: list (@component L)): Prop :=
    match Ps with
      | [] => True
      | [P] => True
      | [P; Q] => compatible2 P Q
      | P :: Ps' => compatible Ps' /\ compatible2 P (link Ps')
    end.

  Lemma compatible_ind:
    forall (P: @component L) (Ps: list component),
      compatible Ps ->
      compatible2 P (link Ps) ->
      compatible (P :: Ps).
  Proof.
    intros P Ps HPs HPPs.
    destruct Ps as [|P' Ps'].
    + exact I.
    + destruct Ps' as [|P'' Ps''].
      * exact HPPs.
      * split.
        { exact HPs. }
        { exact HPPs. }
  Qed.

End Nary.

Arguments link {_} _.
Arguments compatible {_} _.
Arguments compatible_ind {_} _ _ _ _.

Section NaryNeutrLeft.

  Variable L: language.
  Hypothesis Hneutr: neutr_left_hyp L.

  Theorem neutr_left_compatible:
    forall (Ps: list (@component L)),
      compatible Ps ->
      compatible (empty :: Ps).
  Proof.
    intros Ps H.
    apply compatible_ind; try assumption.
    apply neutr_left_compatible2; try assumption.
  Qed.

  Theorem neutr_left_complete_link:
    forall (Ps: list (@component L)),
      compatible Ps ->
      complete (link Ps) ->
      complete (link (empty :: Ps)).
  Admitted.

  Theorem neutr_left_beh_eq_link:
    forall (Ps: list (@component L)),
      compatible Ps ->
      complete (link Ps) ->
      complete (link (empty :: Ps)).
  Admitted.

End NaryNeutrLeft.

Arguments neutr_left_compatible {_} _ _ _.
Arguments neutr_left_complete_link {_} _ _ _ _.
Arguments neutr_left_beh_eq_link {_} _ _ _ _.

Section NaryAssoc.

  Variable L: language.
  Hypothesis Hassoc: assoc_hyp L.
  Definition Hneutr: neutr_left_hyp L := assoc_neutr_left Hassoc.

(*  Theorem assoc_snoc_compatible:
    forall (Ps: list (@component L)) (P: component),
    compatible Ps ->
    compatible2 (link Ps) P ->
    compatible (Ps ++ [P]).
  Admitted.

  Theorem assoc_snoc_complete:
    forall (Ps: list (@component L)) (P: component),
      compatible (Ps ++ [P]) ->
      complete (link2 (link Ps) P) ->
      complete (link (Ps ++ [P])).
  Admitted.

  Theorem assoc_snoc_beh_eq:
    forall (Ps: list (@component L)) (P: component),
      compatible (Ps ++ [P]) ->
      complete (link2 (link Ps) P) ->
      complete (link (Ps ++ [P])).
  Admitted.

  Theorem assoc_compatible:
    forall (Ps Qs: list (@component L)),
      compatible Ps ->
      compatible Qs ->
      compatible2 [link Ps; link Qs] ->
      compatible (Ps ++ Qs).
  Proof.
  Admitted.

  Theorem complete_assoc:
    forall (Ps Qs: list (@component L)),
      compatible (Ps ++ Qs) ->
      (complete (link [link Ps; link Qs]) <->
       complete (link (Ps ++ Qs))).
  Admitted.

  Theorem link_assoc:
    forall (Ps Qs: list (@component L)),
      compatible (Ps ++ Qs) ->
      complete (link (Ps ++ Qs)) ->
      beh_eq (link (Ps ++ Qs)) (link [link Ps; link Qs]).
  Admitted.
 *)

End NaryAssoc.

Section NaryComm.

End NaryComm.
