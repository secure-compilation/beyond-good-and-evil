Require Import Coq.Lists.List.
Import ListNotations.

Require Import MutualDistrust.language.
Require Import MutualDistrust.compiler.
Require Import MutualDistrust.technique.

Section Eqs.

  Variable (L: language).

  Definition stat_eq (P Q: @component L): Prop :=
    forall A, (compatible2 A P /\ complete (link2 A P))
              <->
              (compatible2 A Q /\ complete (link2 A Q)).

  Definition ctx_eq (P Q: @component L): Prop :=
    forall A,
      compatible2 A P /\ complete (link2 A P) ->
      beh_eq (link2 A P) (link2 A Q).

End Eqs.

Arguments stat_eq {_} _ _.
Arguments ctx_eq {_} _ _.

Section Properties.

  Variable C: compiler.

  Hypothesis Hcommsrc: comm_hyp (@source C).
  Definition Hassocsrc: assoc_hyp source := comm_assoc Hcommsrc.
  Definition Hneutrsrc: neutr_left_hyp source := assoc_neutr_left Hassocsrc.

  Hypothesis Hcommtgt: comm_hyp (@target C).
  Definition Hassoctgt: assoc_hyp target := comm_assoc Hcommtgt.
  Definition Hneutrtgt: neutr_left_hyp target := assoc_neutr_left Hassoctgt.

  Definition full_abstraction: Prop :=
    forall (P Q: @component (@source C)),
      stat_eq P Q ->
      stat_eq (compile P) (compile Q) ->
      (ctx_eq P Q <-> ctx_eq (compile P) (compile Q)).

  Definition md1_insertion {L: language} (As: list (@component L)): insertion :=
    insertion_from_map (app As).

  Lemma fa_implies_md1:
    full_abstraction ->
    forall (Ps Qs: list (@component (@source C))),
      compatible Ps ->
      compatible Qs ->
      stat_eq (link Ps) (link Qs) ->
      stat_eq (compile (link Ps)) (compile (link Qs)) ->
      (ctx_eq (link Ps) (link Qs) <-> ctx_eq (compile (link Ps)) (compile (link Qs))).
  Proof.
    intros FA Ps Qs HPs HQs.
    now apply FA.
  Qed.

  Lemma fa_implies_md2:
    full_abstraction ->
    forall (Ps Qs: list (@component (@source C))),
      compatible Ps ->
      compatible Qs ->
      stat_eq (link Ps) (link Qs) ->
      stat_eq (compile (link Ps)) (compile (link Qs)) ->
      (ctx_eq (link Ps) (link Qs) <-> ctx_eq (link (map compile Ps)) (link (map compile Qs))).
  Proof.
    intros FA Ps Qs HPs HQs HsePsQs HsecPsQs.
    assert (ctx_eq (compile (link Ps)) (compile (link Qs))
            <->
            ctx_eq (link (map compile Ps)) (link (map compile Qs))).
    { admit. }
    apply (@iff_trans _ (ctx_eq (compile (link Ps)) (compile (link Qs))) _); try assumption.
    now apply fa_implies_md1.
  Admitted.

  Lemma fa_implies_md3:
    full_abstraction ->
    forall (Ps Qs: list (@component (@source C))),
      compatible Ps ->
      compatible Qs ->
      stat_eq (link Ps) (link Qs) ->
      stat_eq (compile (link Ps)) (compile (link Qs)) ->
      (ctx_eq (link Ps) (link Qs) <-> ctx_eq (link (map compile Ps)) (link (map compile Qs))).
  Proof.
    intros FA Ps Qs HPs HQs HsePsQs HsecPsQs.
    assert (ctx_eq (compile (link Ps)) (compile (link Qs))
            <->
            ctx_eq (link (map compile Ps)) (link (map compile Qs))).
    { admit. }
    apply (@iff_trans _ (ctx_eq (compile (link Ps)) (compile (link Qs))) _); try assumption.
    now apply fa_implies_md1.
  Admitted.

  Record cross_level_equivalence: Type :=
    {
      ins_src:
        list (@component (@source C)) -> list (@component (@source C)) -> @component (@source C);
      ins_tgt:
        list (@component (@target C)) -> list (@component (@source C)) -> @component (@target C);

      prereq:
        list (@component (@source C)) -> list (@component (@source C)) -> Prop;
      ins_hyp_src:
        list (@component (@source C)) -> list (@component (@source C)) -> Prop;
      ins_hyp_tgt:
        list (@component (@target C)) -> list (@component (@source C)) -> Prop;

      prereq_implies_ins_hyp_src:
        forall As Ps Qs, prereq Ps Qs -> ins_hyp_src As Ps -> ins_hyp_src As Qs;
      prereq_implies_ins_hyp_tgt:
        forall as_ Ps Qs, prereq Ps Qs -> ins_hyp_tgt as_ Ps -> ins_hyp_tgt as_ Qs;
      ins_hyp_implies_complete_src:
        forall As Rs, ins_hyp_src As Rs -> complete (ins_src As Rs);
      ins_hyp_implies_complete_tgt:
        forall as_ Rs, ins_hyp_tgt as_ Rs -> complete (ins_tgt as_ Rs)
    }.

  Definition cle_as_prop (cle: cross_level_equivalence): Prop :=
    forall (Ps Qs: list (@component (@source C))),
      prereq cle Ps Qs ->
      ((forall As, ins_hyp_src cle As Ps -> beh_eq (ins_src cle As Ps) (ins_src cle As Qs))
       <->
       (forall as_, ins_hyp_tgt cle as_ Ps -> beh_eq (ins_tgt cle as_ Ps) (ins_tgt cle as_ Qs))).

  Record cle_impl (cle1 cle2: cross_level_equivalence): Prop :=
    {
      prereq_rev_impl: forall Ps Qs, prereq cle2 Ps Qs -> prereq cle1 Ps Qs;
      ins_hyp_src_eq: forall Ps Qs, ins_hyp_src cle1 Ps Qs <-> ins_hyp_src cle2 Ps Qs;
      ins_hyp_tgt_eq: forall Ps Qs, ins_hyp_tgt cle1 Ps Qs <-> ins_hyp_tgt cle2 Ps Qs
    }.

  Lemma technique:
    forall (cle1 cle2: cross_level_equivalence),
      cle_impl cle1 cle2 ->
      cle_as_prop cle1 ->
      cle_as_prop cle2.
    (*(Hlemma1: forall (Ps Qs: list (@component (@source C))),
                       Hf Ps Qs ->
                       ((forall As, H'f _ As Ps -> H'f _ As Qs ->
                                    beh_eq (f _ As Ps) (f _ As Qs))
                        <->
                        (forall as_, H'f _ as_ (map compile Ps) -> H'f _ as_ (map compile Qs) ->
                                     beh_eq (f _ as_ (map compile Ps)) (f _ as_ (map compile Qs)))))
           (Hlemma2: forall (L: language) (Hcomm: comm_hyp L) (Aas Pps Qqs: list (@component L)),
                       H'f _ Aas Pps ->
                       H'g _ Aas Qqs ->
                       beh_eq (f _ Aas Pps) (g _ Aas Qqs))
           (Hlemma3: forall (L: language) (Hcomm: comm_hyp L) (Aas Rrs: list (@component L)),
                       H'f _ Aas Rrs <-> H'g _ Aas Rrs)
           (Hlemma4: forall (L: language) (Hcomm: comm_hyp L) (Aas Rrs: list (@component L)),
                       H'f _ Aas Rrs -> complete (f _ Aas Rrs))
           (Hlemma5: forall (L: language) (Hcomm: comm_hyp L) (Aas Rrs: list (@component L)),
                       H'g _ Aas Rrs -> complete (g _ Aas Rrs))
           (Hlemma6: forall Ps Qs, Hg Ps Qs -> Hf Ps Qs),*)
  Proof.
    intros cle1 cle2 Himpl Hcle1.
    unfold cle_as_prop in *.
    intros Ps Qs Hprereq2.
    assert (prereq cle1 Ps Qs) as Hprereq1.
    { apply (prereq_rev_impl cle1 cle2); try assumption. }
    split.
    + intro Hhl.
      cut (forall as_, ins_hyp_tgt cle1 as_ Ps ->
                       beh_eq (ins_tgt cle1 as_ Ps) (ins_tgt cle1 as_ Qs)).
      { intros Hll as_ Hins2asPs.
        assert (ins_hyp_tgt cle2 as_ Qs) as Hins2asQs.
        { apply (prereq_implies_ins_hyp_tgt cle2 as_ Ps Qs); try assumption. }
        assert (complete (ins_tgt cle2 as_ Ps) /\ complete (ins_tgt cle2 as_ Qs))
          as [Hcompleteins2asPs Hcompleteins2asQs].
        { split; apply ins_hyp_implies_complete_tgt; try assumption. }
        assert (ins_hyp_tgt cle1 as_ Ps /\ ins_hyp_tgt cle1 as_ Qs) as [Hins1asPs Hins1asQs].
        { split; apply ins_hyp_src_eq; try assumption. }
        assert (complete (f _ as_ Ps) /\ complete (f _ as_ Qs))
          as [Hcompleteins1asPs Hcompleteins1asQs].
        { split; apply Hlemma4; try assumption. }
        apply (beh_eq_trans _ (f _ as_ Ps) _); try assumption.
        + apply beh_eq_sym; try assumption.
          apply Hlemma2; try assumption.
        + apply (beh_eq_trans _ (f _ as_ Qs) _); try assumption.
          * apply Hll; try assumption.
          * apply Hlemma2; try assumption. }
      apply Hlemma1; try assumption.
      { intros As Hins1asPs Hins1asQs.
        assert (complete (f _ As Ps) /\ complete (f _ As Qs)) as [Hcompleteins1asPs Hcompleteins1asQs].
        { split; apply Hlemma4; try assumption. }
        assert (H'g _ As Ps /\ H'g _ As Qs) as [Hins2asPs Hins2asQs].
        { split; apply Hlemma3; try assumption. }
        assert (complete (g _ As Ps) /\ complete (g _ As Qs)) as [Hcompleteins2asPs Hcompleteins2asQs].
        { split; apply Hlemma5; try assumption. }
        apply (beh_eq_trans _ (g _ As Ps) _); try assumption.
        + apply Hlemma2; try assumption.
        + apply (beh_eq_trans _ (g _ As Qs) _); try assumption.
          * apply Hhl; try assumption.
          * apply beh_eq_sym; try assumption.
            apply Hlemma2; try assumption. }
    + intro Hll.
      cut (forall As, H'f _ As Ps -> H'f _ As Qs -> beh_eq (f _ As Ps) (f _ As Qs)).
      { intros Hhl As Hins2asPs Hins2asQs.
        assert (complete (g _ As Ps) /\ complete (g _ As Qs)) as [Hcompleteins2asPs Hcompleteins2asQs].
        { split; apply Hlemma5; try assumption. }
        assert (H'f _ As Ps /\ H'f _ As Qs) as [Hins1asPs Hins1asQs].
        { split; apply Hlemma3; try assumption. }
        assert (complete (f _ As Ps) /\ complete (f _ As Qs)) as [Hcompleteins1asPs Hcompleteins1asQs].
        { split; apply Hlemma4; try assumption. }
        apply (beh_eq_trans _ (f _ As Ps) _); try assumption.
        + apply beh_eq_sym; try assumption.
          apply Hlemma2; try assumption.
        + apply (beh_eq_trans _ (f _ As Qs) _); try assumption.
          * apply Hhl; try assumption.
          * apply Hlemma2; try assumption. }
      apply Hlemma1; try assumption.
      { intros as_ Hins1asPs Hins1asQs.
        assert (complete (f _ as_ Ps) /\ complete (f _ as_ Qs))
          as [Hcompleteins1asPs Hcompleteins1asQs].
        { split; apply Hlemma4; try assumption. }
        assert (ins_hyp_tgt cle2 as_ Ps /\ ins_hyp_tgt cle2 as_ Qs)
          as [Hins2asPs Hins2asQs].
        { split; apply Hlemma3; try assumption. }
        assert (complete (g _ as_ Ps) /\ complete (g _ as_ Qs))
          as [Hcompleteins2asPs Hcompleteins2asQs].
        { split; apply Hlemma5; try assumption. }
        apply (beh_eq_trans _ (g _ as_ Ps) _); try assumption.
        + apply Hlemma2; try assumption.
        + apply (beh_eq_trans _ (g _ as_ Qs) _); try assumption.
          * apply Hll; try assumption.
          * apply beh_eq_sym; try assumption.
            apply Hlemma2; try assumption. }
  Qed.


  Record foo :=
    {
      stat_eq: list (@component (@source C)) -> list (@component (@source C)) -> Prop;
      combine: forall L, list (@component L) -> list (@component L) -> @component L;
      combine_hyp: forall L, list (@component L) -> list (@component L) -> Prop;
      combine_hyp_complete: forall L (Aas Rrs: list (@component L)),
                              combine_hyp Aas Rrs -> complete (combine Aas Rrs)
    }.

  Lemma technique:
    forall (f g: forall L, list (@component L) -> list (@component L) -> @component L)
           (Hf Hg: list (@component (@source C)) -> list (@component (@source C)) -> Prop)
           (H'f H'g: forall L, list (@component L) -> list (@component L) -> Prop)
           (Hlemma1: forall (Ps Qs: list (@component (@source C))),
                       Hf Ps Qs ->
                       ((forall As, H'f _ As Ps -> H'f _ As Qs ->
                                    beh_eq (f _ As Ps) (f _ As Qs))
                        <->
                        (forall as_, H'f _ as_ (map compile Ps) -> H'f _ as_ (map compile Qs) ->
                                     beh_eq (f _ as_ (map compile Ps)) (f _ as_ (map compile Qs)))))
           (Hlemma2: forall (L: language) (Hcomm: comm_hyp L) (Aas Pps Qqs: list (@component L)),
                       H'f _ Aas Pps ->
                       H'g _ Aas Qqs ->
                       beh_eq (f _ Aas Pps) (g _ Aas Qqs))
           (Hlemma3: forall (L: language) (Hcomm: comm_hyp L) (Aas Rrs: list (@component L)),
                       H'f _ Aas Rrs <-> H'g _ Aas Rrs)
           (Hlemma4: forall (L: language) (Hcomm: comm_hyp L) (Aas Rrs: list (@component L)),
                       H'f _ Aas Rrs -> complete (f _ Aas Rrs))
           (Hlemma5: forall (L: language) (Hcomm: comm_hyp L) (Aas Rrs: list (@component L)),
                       H'g _ Aas Rrs -> complete (g _ Aas Rrs))
           (Hlemma6: forall Ps Qs, Hg Ps Qs -> Hf Ps Qs),
      (forall (Ps Qs: list (@component (@source C))),
         Hg Ps Qs ->
         ((forall As, H'g _ As Ps -> H'g _ As Qs ->
                      beh_eq (g _ As Ps) (g _ As Qs))
          <->
          (forall as_, H'g _ as_ (map compile Ps) ->
                       H'g _ as_ (map compile Qs) ->
                       beh_eq (g _ as_ (map compile Ps)) (g _ as_ (map compile Qs))))).
  Proof.
    intros f g Hf Hg H'f H'g.
    intros Hlemma1 Hlemma2 Hlemma3 Hlemma4 Hlemma5 Hlemma6 Ps Qs HgPsQs.
    assert (Hf Ps Qs).
    { apply Hlemma6; try assumption. }
    split.
    + intro Hhl.
      cut (forall as_, H'f _ as_ (map compile Ps) ->
                       H'f _ as_ (map compile Qs) ->
                       beh_eq (f _ as_ (map compile Ps)) (f _ as_ (map compile Qs))).
      { intros Hll as_ HgasPs HgasQs.
        assert (complete (g _ as_ (map compile Ps)) /\ complete (g _ as_ (map compile Qs)))
          as [HcompletegasPs HcompletegasQs].
        { split; apply Hlemma5; try assumption. }
        assert (H'f _ as_ (map compile Ps) /\ H'f _ as_ (map compile Qs)) as [H'fasPs H'fasQs].
        { split; apply Hlemma3; try assumption. }
        assert (complete (f _ as_ (map compile Ps)) /\ complete (f _ as_ (map compile Qs)))
          as [HcompletefasPs HcompletefasQs].
        { split; apply Hlemma4; try assumption. }
        apply (beh_eq_trans _ (f _ as_ (map compile Ps)) _); try assumption.
        + apply beh_eq_sym; try assumption.
          apply Hlemma2; try assumption.
        + apply (beh_eq_trans _ (f _ as_ (map compile Qs)) _); try assumption.
          * apply Hll; try assumption.
          * apply Hlemma2; try assumption. }
      apply Hlemma1; try assumption.
      { intros As HfAsPs HfAsQs.
        assert (complete (f _ As Ps) /\ complete (f _ As Qs)) as [HcompletefAsPs HcompletefAsQs].
        { split; apply Hlemma4; try assumption. }
        assert (H'g _ As Ps /\ H'g _ As Qs) as [H'gAsPs H'gAsQs].
        { split; apply Hlemma3; try assumption. }
        assert (complete (g _ As Ps) /\ complete (g _ As Qs)) as [HcompletegAsPs HcompletegAsQs].
        { split; apply Hlemma5; try assumption. }
        apply (beh_eq_trans _ (g _ As Ps) _); try assumption.
        + apply Hlemma2; try assumption.
        + apply (beh_eq_trans _ (g _ As Qs) _); try assumption.
          * apply Hhl; try assumption.
          * apply beh_eq_sym; try assumption.
            apply Hlemma2; try assumption. }
    + intro Hll.
      cut (forall As, H'f _ As Ps -> H'f _ As Qs -> beh_eq (f _ As Ps) (f _ As Qs)).
      { intros Hhl As HgAsPs HgAsQs.
        assert (complete (g _ As Ps) /\ complete (g _ As Qs)) as [HcompletegAsPs HcompletegAsQs].
        { split; apply Hlemma5; try assumption. }
        assert (H'f _ As Ps /\ H'f _ As Qs) as [H'fAsPs H'fAsQs].
        { split; apply Hlemma3; try assumption. }
        assert (complete (f _ As Ps) /\ complete (f _ As Qs)) as [HcompletefAsPs HcompletefAsQs].
        { split; apply Hlemma4; try assumption. }
        apply (beh_eq_trans _ (f _ As Ps) _); try assumption.
        + apply beh_eq_sym; try assumption.
          apply Hlemma2; try assumption.
        + apply (beh_eq_trans _ (f _ As Qs) _); try assumption.
          * apply Hhl; try assumption.
          * apply Hlemma2; try assumption. }
      apply Hlemma1; try assumption.
      { intros as_ HfasPs HfasQs.
        assert (complete (f _ as_ (map compile Ps)) /\ complete (f _ as_ (map compile Qs)))
          as [HcompletefasPs HcompletefasQs].
        { split; apply Hlemma4; try assumption. }
        assert (H'g _ as_ (map compile Ps) /\ H'g _ as_ (map compile Qs))
          as [H'gasPs H'gasQs].
        { split; apply Hlemma3; try assumption. }
        assert (complete (g _ as_ (map compile Ps)) /\ complete (g _ as_ (map compile Qs)))
          as [HcompletegasPs HcompletegasQs].
        { split; apply Hlemma5; try assumption. }
        apply (beh_eq_trans _ (g _ as_ (map compile Ps)) _); try assumption.
        + apply Hlemma2; try assumption.
        + apply (beh_eq_trans _ (g _ as_ (map compile Qs)) _); try assumption.
          * apply Hll; try assumption.
          * apply beh_eq_sym; try assumption.
            apply Hlemma2; try assumption. }
  Qed.

  Lemma fa_implies_md4:
    full_abstraction ->
    forall (Ps Qs: list (@component (@source C))),
      compatible Ps ->
      compatible Qs ->
      stat_eq (link Ps) (link Qs) ->
      stat_eq (compile (link Ps)) (compile (link Qs)) ->
      ((forall As, compatible As -> compatible2 (link As) (link Ps) ->
                   (link Ps) (link Qs)
       <->
       ctx_eq (link (map compile Ps)) (link (map compile Qs))).
  Proof.
    intros FA Ps Qs HPs HQs HsePsQs HsecPsQs.
    assert (ctx_eq (compile (link Ps)) (compile (link Qs))
            <->
            ctx_eq (link (map compile Ps)) (link (map compile Qs))).
    { admit. }
    apply (@iff_trans _ (ctx_eq (compile (link Ps)) (compile (link Qs))) _); try assumption.
    now apply fa_implies_md1.
  Admitted.


  Lemma fa_implies_md0:
    full_abstraction ->
    forall (Ps Qs: list (@component (@source C))),
      compatible Ps ->
      compatible Qs ->
      (forall As,
         compatible As ->
         ((compatible2 (link As) (link Ps) /\ complete (link2 (link As) (link Ps)))
          <->
          (compatible2 (link As) (link Qs) /\ complete (link2 (link As) (link Qs))))) ->
      (forall as_,
         compatible as_ ->
         ((compatible2 (link as_) (compile (link Ps)) /\ complete (link2 (link as_) (compile (link Ps))))
          <->
          (compatible2 (link as_) (compile (link Qs)) /\ complete (link2 (link as_) (compile (link Qs)))))) ->
      ((forall As, compatible2 (link As) (link Ps) /\ complete (link2 (link As) (link Ps)) ->
                   beh_eq (link2 (link As) (link Ps)) (link2 (link As) (link Qs)))
       <->
       (forall as_, compatible2 (link as_) (compile (link Ps)) /\ complete (link2 (link as_) (compile (link Ps))) ->
                    beh_eq (link2 (link as_) (compile (link Ps))) (link2 (link as_) (compile (link Qs))))).
  Proof.
    intros FA Ps Qs HPs HQs.
    apply (FA (link Ps) (link Qs)).
    exact (FA (link Ps) (link Qs)).

  (*Definition mutual_distrust (n_att: nat): Prop :=
    forall (Ps Qs: list (@component (@source C))),
      compatible Ps ->
      compatible Qs ->
      stat_eq (link Ps) (link Qs) ->
      stat_eq (compile (link Ps)) (compile (link Qs)) ->
      ((forall As AsPs,
          length As = n_att ->
          compatible (As ++ Ps) ->
          complete (link (As ++ Ps)) ->
          Permutation AsPs (As ++ Ps) ->
          Permutation AsQs (As ++ Qs) ->
          beh_eq AsPs AsQs)
       <->
       (forall As AsPs,
          length As = n_att ->
          compatible (As ++ (map compile Ps)) ->
          complete (link (As ++ Ps)) ->
          Permutation AsPs (As ++ Ps) ->
          Permutation AsQs (As ++ Qs) ->
          beh_eq AsPs AsQs)).*)

End Properties.

Arguments full_abstraction {_}.
Arguments mutual_distrust {_}.


(*Lemma full_abstraction:
    full_abstraction C ->
    forall Ps Qs,
      stat_eq Ps Qs ->
      (forall As, compatible Ps As -> complete (link [link As; link Ps]))
      <->
      (forall as_, compatible Ps as_ -> complete (link [link as_; link (map compile Ps)]))


  Theorem fa_implies_md:
    forall .

Definition insertion_1 {L: language} (As: list (component L)) :=
  from_map (app As).

  insertion (LP LA: language): Type :=
  {
    insertable: list (component LP) -> Prop;
    insert: list (component LP) -> component LA
  }.*)
