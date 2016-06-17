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

(* If a[P↓] ≁L a[Q↓] we say that a distinguish the partial
   programs P↓ and Q↓. The same concept exists for ≁H *)

Lemma low_neq_symmetry :
  forall P Q,
  neq_progL P Q -> neq_progL Q P.
Proof.
  intros. inversion H. constructor.
  destruct H0.
  - right. apply and_comm. apply H0.
  - left. apply and_comm. apply H0.
Qed.

Lemma high_neq_symmetry :
  forall P Q,
  neq_progH P Q -> neq_progH Q P.
Proof.
  intros. inversion H. constructor.
  destruct H0.
  - right. apply and_comm. apply H0.
  - left. apply and_comm. apply H0.
Qed.

(* _____________________________________ 
           LEMMAS & PROPERTIES
   _____________________________________ *)

(* ------- Canonicalization ------- *)
(** Already proved **)
Lemma canonicalization :
  forall t s, wellformed_shape s ->
  forall P, (PROGRAM_SHAPE P ∈• s) -> 
    (program_fully_defined s P) ->
    (in_Traces_p t (COMPILE_PROG P↓) s
      <-> 
     in_Traces_p (zetaC_t t) (COMPILE_PROG P↓) s).
Proof.
Admitted.

(* ------- Definability / Trace mappping algorithm ------- *)
(** An OCaml algorithm is available **)
Lemma definability :
  forall t g1 s, wellformed_shape s ->
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

(* ---- Compiled fully defined k yield canonical actions ---- *)
Lemma only_yield_canonical_actions :
  forall s A t,
    wellformed_shape s /\ CONTEXT_SHAPE A ∈∘ s ->
    context_fully_defined s A ->
    in_Traces_a t (COMPILE_PROG A↓) s ->
    t = zetaC_t t.
Proof.
Admitted.

Definition structured_full_abstraction : Prop :=
  forall s, wellformed_shape s ->
  forall P Q, 
    (PROGRAM_SHAPE P ∈• s) ->
    (PROGRAM_SHAPE Q ∈• s) ->
    (program_fully_defined s P) ->
    (program_fully_defined s Q) ->
    (exists a, (LL_CONTEXT_SHAPE a ∈∘ s) /\
       let ap := (LL_context_application a (COMPILE_PROG P↓)) in
       let aq := (LL_context_application a (COMPILE_PROG Q↓)) in
       LOW_NEQ ap ≁L aq)
    ->
    (exists A,
    let AP := (context_application A P) in
    let AQ := (context_application A Q) in
    (CONTEXT_SHAPE A ∈∘ s) /\ (context_fully_defined s A) ->
    HIGH_NEQ AP ≁H AQ).

(* Equal to the previous one by prenex normal form transformation *)
Definition structured_full_abstraction_aux 
  (a : Target.program) (P Q : Source.partial_program)
  (s:shape) : Prop :=
    wellformed_shape s ->
    (PROGRAM_SHAPE P ∈• s) ->
    (PROGRAM_SHAPE Q ∈• s) ->
    (program_fully_defined s P) ->
    (program_fully_defined s Q) ->
    ((LL_CONTEXT_SHAPE a ∈∘ s) /\
       let ap := (LL_context_application a (COMPILE_PROG P↓)) in
       let aq := (LL_context_application a (COMPILE_PROG Q↓)) in
       LOW_NEQ ap ≁L aq)
    ->
    (exists A,
    let AP := (context_application A P) in
    let AQ := (context_application A Q) in
    (CONTEXT_SHAPE A ∈∘ s) /\ (context_fully_defined s A) ->
    HIGH_NEQ AP ≁H AQ).

Definition separate_compilation_correctness : Prop :=
  forall s, wellformed_shape s ->
  forall A P, 
    (CONTEXT_SHAPE A ∈∘ s) ->
    (PROGRAM_SHAPE P ∈• s) ->
    program_fully_defined s P ->
    context_fully_defined s A ->
    (* 1 *)
    ((program_terminates (context_application A P)
    <-> cprogram_terminates (LL_context_application 
    (COMPILE_PROG A↓) (COMPILE_PROG P↓))) 
      /\
    (* 2 *)
    (program_diverges (context_application A P)
    <-> cprogram_diverges (LL_context_application 
    (COMPILE_PROG A↓) (COMPILE_PROG P↓)))).

(* _____________________________________ 
   SECURE COMPARTMENTALIZING COMPILATION
            AND PROOFS OF LEMMAS
   _____________________________________ *)

Lemma shape_closed_under_compilation_program :
  forall s P, PROGRAM_SHAPE P ∈• s 
  -> LL_PROGRAM_SHAPE (COMPILE_PROG P↓) ∈• s.
Proof.
Admitted.

Lemma shape_closed_under_compilation_context :
  forall s A, CONTEXT_SHAPE A ∈∘ s 
  -> LL_CONTEXT_SHAPE (COMPILE_PROG A↓) ∈∘ s.
Proof.
Admitted.

Definition is_a_prefix_of (u:trace) (t:trace) : Prop :=
  exists v, u++v = t.

Definition is_longest_prefix_of (u:trace)
  (t:trace) (p: program) (s:shape) : Prop :=
  (is_a_prefix_of u t /\ in_Traces_p u p s) /\
  (forall v, is_a_prefix_of v t /\ in_Traces_p v p s ->
               is_a_prefix_of v u).

Hypothesis longest_prefix_of :
  trace -> program -> shape -> trace.

Hypothesis longest_prefix_of_spec :
  forall t p s,
    let u := longest_prefix_of t p s in
    (is_longest_prefix_of u t p s).

Lemma twolist_posibilities :
  forall {X:Type} (t u : X) (t' u' : list X),
  [t; u] = t' ++ u' ->
  (t' = [] /\ u' = [t]++[u]) \/
  (t' = [t]++[u] /\ u' = []) \/
  (t' = [t] /\ u' = [u]).
Proof.
  intros. generalize dependent u'.
  induction t'.
  - intros. left. split.
    + reflexivity.
    + rewrite app_nil_l in H. symmetry. apply H.
  - intros. induction u'.
    + simpl. right. left. split.
      * symmetry. rewrite app_nil_r in H. apply H.
      * reflexivity.
    + simpl in *. inversion H. symmetry in H2.
      apply app_eq_unit in H2. destruct H2.
      * right. right. destruct H0. rewrite H0.
        split. reflexivity. apply H2.
      * destruct H0. right. left.
        rewrite H0. split. reflexivity. apply H2. 
Qed.

Lemma trace_sets_closed_under_prefix_program :
  forall t' t p s, (LL_PROGRAM_SHAPE p ∈• s) ->
    is_a_prefix_of t' t -> in_Traces_p t p s ->
    in_Traces_p t' p s.
Proof.
  intros.
  destruct p as [[Isp mem] E].
  destruct s as [Is comps].
  unfold is_a_prefix_of in H0.
  destruct H0 as [trace H_t].
  rewrite <- H_t in H1. unfold in_Traces_p in H1.
  destruct H1. inversion H0.
  - unfold in_Traces_p. exists o'.
    symmetry in H4. apply app_eq_nil in H4.
    destruct H4. rewrite H3. constructor.
  - unfold in_Traces_p. exists o'.
    symmetry in H1. apply app_eq_nil in H1.
    destruct H1. rewrite H1. constructor.
  - unfold in_Traces_p. exists o'.
    symmetry in H1. apply app_eq_unit in H1.
    destruct H1.
    + destruct H1. rewrite H1. constructor.
    + destruct H1. rewrite H1. constructor.
      rewrite H3. apply H4.
  - unfold in_Traces_p. apply twolist_posibilities in H1.
    destruct H1 as [H1 | H1].
    + exists o'. destruct H1. rewrite H1. constructor.
    + destruct H1.
      * exists x. destruct H1. rewrite H6 in H0.
        rewrite app_nil_r in H0. apply H0.
      * exists o'. destruct H1. rewrite H1.
        apply H2.
Qed.

Lemma trace_sets_closed_under_prefix_context :
  forall t' t a s, (LL_CONTEXT_SHAPE a ∈∘ s) ->
    is_a_prefix_of t' t -> in_Traces_a t a s ->
    in_Traces_p t' a s.
Proof.
  intros.
  destruct a as [[Isp mem] E].
  destruct s as [Is comps].
  unfold is_a_prefix_of in H0.
  destruct H0 as [trace H_t].
  rewrite <- H_t in H1. unfold in_Traces_a in H1.
  destruct H1. inversion H0.
  - unfold in_Traces_a. exists o'.
    symmetry in H4. apply app_eq_nil in H4.
    destruct H4. rewrite H3. constructor.
  - unfold in_Traces_a. exists o'.
    symmetry in H1. apply app_eq_nil in H1.
    destruct H1. rewrite H1. constructor.
  - unfold in_Traces_a. exists o'.
    symmetry in H1. apply app_eq_unit in H1.
    destruct H1.
    + destruct H1. rewrite H1. constructor.
    + destruct H1. rewrite H1. constructor.
      rewrite H3. apply H4.
  - unfold in_Traces_a. apply twolist_posibilities in H1.
    destruct H1 as [H1 | H1].
    + exists o'. destruct H1. rewrite H1. constructor.
    + destruct H1.
      * exists x. destruct H1. rewrite H6 in H0.
        rewrite app_nil_r in H0. apply H0.
      * exists o'. destruct H1. rewrite H1.
        apply H2.
Qed.

Lemma app_is_cons :
  forall {X:Type} a (l:list X), a::l = [a]++l.
Proof.
  intros. reflexivity.
Qed.

Lemma zeta_linear_program :
  forall t g,
  zetaC_t (t ++ [Ext g ProgramOrigin]) =
  zetaC_t t ++ [Ext g ProgramOrigin].
Proof.
  intros.
  induction t.
  - simpl. reflexivity.
  - rewrite app_is_cons. rewrite <- app_assoc.
    destruct a; destruct o;
    simpl; rewrite IHt; reflexivity.
Qed.

Lemma clear_regs_aux_idempotent :
  forall l k n, clear_regs_aux l k n =
  clear_regs_aux (clear_regs_aux l k n) k n.
Proof.
  induction l.
  - auto.
  - intros k n. simpl.
    rewrite <- IHl. destruct (eq_nat_dec n k); auto.
Qed.

Lemma clear_regs_idempotent : 
  forall l, clear_regs l = clear_regs (clear_regs l).
Proof.
  intros. unfold clear_regs.
  rewrite <- clear_regs_aux_idempotent. auto.
Qed.

Lemma zeta_gamma_idempotent :
  forall e,
  zeta_gamma e = zeta_gamma (zeta_gamma e).
Proof.
  intros. destruct e;
  try (simpl; rewrite <- clear_regs_idempotent; reflexivity).
  simpl. reflexivity.
Qed.

Lemma zetaC_t_idempotent :
  forall t, zetaC_t t = zetaC_t (zetaC_t t).
Proof.
  intros. induction t.
  - reflexivity.
  - destruct a; destruct o; simpl; try (reflexivity);
    try (rewrite <- zeta_gamma_idempotent);
    rewrite <- IHt; reflexivity.
Qed.

Lemma program_Ea_immuable_to_zeta :
  forall t g1,
  zetaC_t (t ++ [Ext g1 ProgramOrigin])
  = zetaC_t (t) ++ [Ext g1 ProgramOrigin].
Proof.
  intros.
  rewrite zeta_linear_program.
  reflexivity.
Qed.

Lemma trace_post_terminaison :
  forall t a p s o,
  ~(in_Traces_p (t++[Ext End o]++[a]) p s).
Proof.
  intros. intro contra.
  destruct s as [Is comps].
  destruct p as [[Isp mem] E].
  unfold in_Traces_p in contra. destruct contra.
  inversion H.
  - symmetry in H3. apply app_eq_nil in H3.
    destruct H3. inversion H3.
  - symmetry in H0. apply app_eq_nil in H0.
    destruct H0. inversion H4.
  - symmetry in H0. apply app_eq_unit in H0.
    destruct H0. destruct H0. inversion H4.
    destruct H0. inversion H4.
  - symmetry in H0. rewrite app_is_cons in H0.
    rewrite app_assoc in H0.
    assert ([t0; u] = [t0]++[u]). reflexivity.
    rewrite H5 in H0. apply app_inj_tail in H0.
    destruct H0. apply app_eq_unit in H0.
    destruct H0; destruct H0; inversion H7.
    + rewrite H0 in H. rewrite app_nil_l in H.
      rewrite <- H9 in H1. rewrite <- H6 in H4.
      inversion H1. inversion H12.
      destruct (decode (fetch_mem C mem0 pc)).
      * destruct i; inversion H15.
      * inversion H15.
      * rewrite <- H14 in H4. inversion H4. inversion H20.
      * rewrite <- H16 in H4. inversion H4. inversion H21.
Qed.

Theorem contrapositive : forall P Q : Prop, 
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  intro contra.
  apply H in contra.
  apply H0 in contra.
  contradiction.
Qed.

Theorem separate_compilation_correctness_proof :
  separate_compilation_correctness.
Proof.
Admitted.

(* We suppose that a[P↓] terminates and a[Q↓] diverges *)
Lemma structured_full_abstraction_aux_proof :
  forall a P Q s,
  let ap := (LL_context_application a COMPILE_PROG P↓) in
  let aq := (LL_context_application a COMPILE_PROG Q↓) in
  cprogram_terminates ap -> cprogram_diverges aq ->
  structured_full_abstraction_aux a P Q s.
Proof.
  unfold structured_full_abstraction_aux.
  intros a P Q s ap_terminates aq_diverges WF_s
    H_shP H_shQ H_PFD H_QFD.
  (* We consider a ∈∘ s distinguishing P ∈• s and Q ∈• s *)
  intros H_a. destruct H_a as [H_sha H_low_neq].
  inversion H_low_neq as [ap aq H_behavior ap_eq aq_eq].
  (* Goal : build a full-defined A ∈∘ s such that A[P] ≁ A[Q] *)
  (* We first apply trace decomposition *)
  assert (H_shq := H_shQ).
  apply shape_closed_under_compilation_program in H_shq.
  assert (H_shp := H_shP).
  apply shape_closed_under_compilation_program in H_shp.
  pose (trace_decomposition s (COMPILE_PROG P↓) 
    H_shp a H_sha ap_terminates) as t_decomposition.
  destruct t_decomposition as [ti H_decomposition].
  (* We call tp the longest prefix of ti such that tp ∈ Tr•s(a) *)
  assert (exists tp, is_longest_prefix_of tp ti
    (COMPILE_PROG Q↓) s) as tp_exists.
  Case "Proof of existence of tp".
  { exists (longest_prefix_of ti (COMPILE_PROG Q↓) s).
    apply longest_prefix_of_spec. }
  destruct tp_exists as [tp H_tp].
  unfold is_longest_prefix_of in H_tp.
  destruct H_tp as [H_tp H_tp3].
  destruct H_tp as [H_tp H_tp2].
  unfold is_a_prefix_of in H_tp. inversion H_tp as [v H_prefix].
  assert (is_a_prefix_of tp ti) as H_tp1.
  { rewrite <- H_prefix. unfold is_a_prefix_of.
    exists v. reflexivity. }
  destruct H_decomposition as [t' [o]].
  destruct H as [H_tEnd H_tSets].
  destruct H_tSets as [H_tSets1 H_tSets2].
  (* We know that tp ∈ Tr∘s(P↓) ∩ Tr•s(a) *)
  assert ((in_Traces_p tp (COMPILE_PROG P↓) s)
       /\ (in_Traces_a tp a s)) as H_tp_in_Pa.
  Case "Proof of tp ∈ Tr∘s(P↓) ∩ Tr•s(a)".
  { split.
    apply (trace_sets_closed_under_prefix_program
      tp ti (COMPILE_PROG P↓) s H_shp H_tp1 H_tSets1).
    apply (trace_sets_closed_under_prefix_context
      tp ti a s H_sha H_tp1 H_tSets2). }
  (* tp is a strict prefix *)
  assert (tp <> ti) as strict_prefix.
  Case "Proof of distinction between tp and ti".
  { unfold not. intro contra.
    assert (in_Traces_p ti COMPILE_PROG Q ↓ s /\
      in_Traces_a ti a s) as H_and.
    { split. rewrite contra in H_tp2. apply H_tp2. apply H_tSets2. }
    assert ((forall (Ea : external_action) (o : origin),
      ~(in_Traces_p (ti ++ [Ext Ea o]) COMPILE_PROG Q ↓ s /\
      in_Traces_a (ti ++ [Ext Ea o]) a s))) as Hassert.
    { intros. intro contra_assert. destruct contra_assert.
      rewrite H_tEnd in H0. rewrite <- app_assoc in H0.
      apply trace_post_terminaison in H0. contradiction. }
    pose (trace_composition ti s (COMPILE_PROG Q↓)
      H_shq a H_sha H_and Hassert) as t_composition.
    destruct t_composition as [t_compositionL t_compositionR].
    assert (cprogram_terminates
      (LL_context_application a COMPILE_PROG Q ↓)) as H_absurd.
    { apply t_compositionR. exists t'. exists o. apply H_tEnd. }
    assert (
      cprogram_terminates 
        (LL_context_application a COMPILE_PROG Q ↓) /\
      cprogram_diverges 
        (LL_context_application a COMPILE_PROG Q ↓))
      as absurd.
    split. apply H_absurd. apply aq_diverges.
    apply (LL_program_behavior_exclusion
      (LL_context_application a COMPILE_PROG Q ↓)) in absurd.
    contradiction. }
  (* There exists Ea such that tp.Ea such that tp.Ea 
     is a prefix of ti *)
  assert (exists Ea g1 o, is_a_prefix_of (tp++Ea) ti /\ 
    Ea = [Ext g1 o]) as Ea_exists.
  { admit.
    (* TODO : Use the fact that tp is a strict prefix
      so there exists an other action following it *) }
  destruct Ea_exists as [Ea H_EaExists].
  destruct H_EaExists as [g1 H_EaExists].
  destruct H_EaExists as [origin_Ea H_EaExists].
  destruct H_EaExists as [H_EaExists H_g1].
  (* Ea is a program action *)
  assert (origin_Ea = ProgramOrigin)
    as H_program_action.
  { destruct origin_Ea.
    (* Ea cannot be a context action *)
    pose (trace_extensibility tp s g1 (COMPILE_PROG Q↓)
    H_shq a H_sha) as t_extensibility.
    destruct t_extensibility as [t_ext1 t_ext2].
    assert (in_Traces_p tp COMPILE_PROG Q ↓ s /\
      in_Traces_a (tp ++ [Ext g1 ContextOrigin]) a s)
      as H_assert.
    { split. assumption. rewrite <- H_g1.
      apply (trace_sets_closed_under_prefix_context
        (tp++Ea) ti a s H_sha H_EaExists H_tSets2). }
    apply t_ext1 in H_assert.
    pose (H_tp3' := H_tp3).
    specialize (H_tp3' (tp ++ [Ext g1 ContextOrigin])).
    rewrite H_g1 in H_EaExists.
    specialize (H_tp3' (conj H_EaExists H_assert)).
    unfold is_a_prefix_of in H_tp3'. destruct H_tp3'.
    rewrite <- app_assoc in H.
    rewrite <- (app_nil_r tp) in H.
    assert ((tp ++ []) ++ [Ext g1 ContextOrigin] ++ x
      = tp ++ [Ext g1 ContextOrigin] ++ x) as H_a.
    { rewrite (app_nil_r tp). reflexivity. }
    rewrite H_a in H. clear H_a.
    apply app_inv_head in H. inversion H.
    (* Ea is a program action *)
    reflexivity. }
  rewrite H_program_action in H_g1.
  (* Let tc be the canonicalization of tp *)
  pose (tc := zetaC_t tp).
  (* tc is a trace of P↓ *)
  pose (canonicalization (tp++Ea) s WF_s P H_shP H_PFD)
    as H_canonicalization.
  destruct H_canonicalization as [H_canon1 H_canon2].
  assert (in_Traces_p (tp ++ Ea) COMPILE_PROG P ↓ s)
    as H_zeta.
  { apply (trace_sets_closed_under_prefix_program
      (tp++Ea) ti (COMPILE_PROG P↓) s H_shp H_EaExists
      H_tSets1). }
  apply H_canon1 in H_zeta.
  (* Use of the definability assumption to build A *)
  pose (definability tc g1 s) as H_definability.
  assert (tc = zetaC_t tc /\
    (exists p : program, LL_PROGRAM_SHAPE p ∈• s ->
    in_Traces_p (tc ++ [Ext g1 ProgramOrigin]) p s)) 
    as H_definability_premises.
  Case "Proof of premises of definability".
  { split.
    unfold tc. rewrite <- zetaC_t_idempotent. reflexivity.
    exists (COMPILE_PROG P↓). intros H_def. unfold tc.
    rewrite <- (program_Ea_immuable_to_zeta tp g1).
    rewrite <- H_g1. apply H_zeta. }
  specialize (H_definability WF_s H_definability_premises).
  destruct H_definability as 
    [A [H_shA [H_AFD [H_def1 [H_def2 H_def3]]]]].
  assert (H_sha' := H_shA).
  apply shape_closed_under_compilation_context in H_sha'.
  (* Now, we want to show that A↓[P↓] terminates while
     A↓[Q↓] diverges with the A generated by definability *)
  (* We first prove that A↓[P↓] terminates *)
  assert (cprogram_terminates (LL_context_application
    (COMPILE_PROG A↓) (COMPILE_PROG P↓))) as AP_terminates.
  Case "that A↓[P↓] terminates".
  { destruct g1 eqn:HD_g1.
    SCase "g1 = ExtCall".
    { assert (ExtCall c p r <> ✓) as Hassert.
      intro contra. inversion contra.
      apply H_def2 in Hassert.
      rename Hassert into H_context_action.
      apply H_canon2 in H_zeta.
      rewrite H_g1 in H_zeta.
      (* Apply trace extensibility to P↓ *)
      pose (trace_extensibility 
        (tc ++ [Ext (ExtCall c p r) ProgramOrigin]) s ✓
        (COMPILE_PROG P↓) H_shp (COMPILE_PROG A↓) H_sha')
        as t_extensibility.
      destruct t_extensibility as [t_ext1 t_ext2].
      assert (in_Traces_p
           (tc ++ [Ext (ExtCall c p r) ProgramOrigin])
           COMPILE_PROG P ↓ s /\
         in_Traces_a
           ((tc ++ [Ext (ExtCall c p r) ProgramOrigin]) ++
            [Ext ✓ ContextOrigin]) COMPILE_PROG A ↓ s)
      as ext_premise.
      { split.
        rewrite <- H_g1 in H_zeta. apply H_canon1 in H_zeta.
        rewrite H_g1 in H_zeta.
        rewrite program_Ea_immuable_to_zeta in H_zeta.
        apply H_zeta.
        rewrite <- app_assoc. apply H_context_action. }
      apply t_ext1 in ext_premise.
      (* Apply trace composition *)
      pose (trace_composition
        ((tc ++ [Ext (ExtCall c p r) ProgramOrigin]) ++
        [Ext ✓ ContextOrigin]) s (COMPILE_PROG P↓)
        H_shp (COMPILE_PROG A↓) H_sha')
        as t_composition.
      assert (in_Traces_p
        ((tc ++ [Ext (ExtCall c p r) ProgramOrigin]) ++
        [Ext ✓ ContextOrigin]) COMPILE_PROG P ↓ s /\
        in_Traces_a
        ((tc ++ [Ext (ExtCall c p r) ProgramOrigin]) ++
        [Ext ✓ ContextOrigin]) COMPILE_PROG A ↓ s)
        as t_composition_premise.
      { split. apply ext_premise.
        rewrite <- app_assoc. apply H_context_action. }
      specialize (t_composition t_composition_premise).
      assert ((forall (Ea : external_action) (o : origin),
        ~(in_Traces_p (((tc ++ [Ext (ExtCall c p r) ProgramOrigin]) ++
          [Ext ✓ ContextOrigin]) ++ 
          [Ext Ea o]) COMPILE_PROG P ↓ s /\
        in_Traces_a (((tc ++ [Ext (ExtCall c p r) ProgramOrigin]) ++
          [Ext ✓ ContextOrigin]) ++ 
          [Ext Ea o]) COMPILE_PROG A ↓ s)))
        as t_composition_premise'.
      { intros. intro contra_assert. destruct contra_assert.
        pose (trace_post_terminaison 
          (tc ++ [Ext (ExtCall c p r) ProgramOrigin])
          (Ext Ea0 o0) (COMPILE_PROG P↓) s ContextOrigin)
          as H_absurd.
        rewrite app_assoc in H_absurd.
        apply H_absurd in H. contradiction. }
      specialize (t_composition t_composition_premise').
      clear t_composition_premise; clear t_composition_premise'.
      destruct t_composition as [t_comp1 t_comp2].
      apply t_comp2.
      exists (tc ++ [Ext (ExtCall c p r) ProgramOrigin]).
      exists ContextOrigin. reflexivity. }
    SCase "g1 = ExtRet".
    { assert (ExtRet r <> ✓) as Hassert.
      intro contra. inversion contra.
      apply H_def2 in Hassert.
      rename Hassert into H_context_action.
      apply H_canon2 in H_zeta.
      rewrite H_g1 in H_zeta.
      (* Apply trace extensibility to P↓ *)
      pose (trace_extensibility 
        (tc ++ [Ext (ExtRet r) ProgramOrigin]) s ✓
        (COMPILE_PROG P↓) H_shp (COMPILE_PROG A↓) H_sha')
        as t_extensibility.
      destruct t_extensibility as [t_ext1 t_ext2].
      assert (in_Traces_p
           (tc ++ [Ext (ExtRet r) ProgramOrigin])
           COMPILE_PROG P ↓ s /\
         in_Traces_a
           ((tc ++ [Ext (ExtRet r) ProgramOrigin]) ++
            [Ext ✓ ContextOrigin]) COMPILE_PROG A ↓ s)
      as ext_premise.
      { split.
        rewrite <- H_g1 in H_zeta. apply H_canon1 in H_zeta.
        rewrite H_g1 in H_zeta.
        rewrite program_Ea_immuable_to_zeta in H_zeta.
        apply H_zeta.
        rewrite <- app_assoc. apply H_context_action. }
      apply t_ext1 in ext_premise.
      (* Apply trace composition *)
      pose (trace_composition
        ((tc ++ [Ext (ExtRet r) ProgramOrigin]) ++
        [Ext ✓ ContextOrigin]) s (COMPILE_PROG P↓)
        H_shp (COMPILE_PROG A↓) H_sha')
        as t_composition.
      assert (in_Traces_p
        ((tc ++ [Ext (ExtRet r) ProgramOrigin]) ++
        [Ext ✓ ContextOrigin]) COMPILE_PROG P ↓ s /\
        in_Traces_a
        ((tc ++ [Ext (ExtRet r) ProgramOrigin]) ++
        [Ext ✓ ContextOrigin]) COMPILE_PROG A ↓ s)
        as t_composition_premise.
      { split. apply ext_premise.
        rewrite <- app_assoc. apply H_context_action. }
      specialize (t_composition t_composition_premise).
      assert ((forall (Ea : external_action) (o : origin),
        ~(in_Traces_p (((tc ++ [Ext (ExtRet r) ProgramOrigin]) ++
          [Ext ✓ ContextOrigin]) ++ 
          [Ext Ea o]) COMPILE_PROG P ↓ s /\
        in_Traces_a (((tc ++ [Ext (ExtRet r) ProgramOrigin]) ++
          [Ext ✓ ContextOrigin]) ++ 
          [Ext Ea o]) COMPILE_PROG A ↓ s)))
        as t_composition_premise'.
      { intros. intro contra_assert. destruct contra_assert.
        pose (trace_post_terminaison 
          (tc ++ [Ext (ExtRet r) ProgramOrigin])
          (Ext Ea0 o0) (COMPILE_PROG P↓) s ContextOrigin)
          as H_absurd.
        rewrite app_assoc in H_absurd.
        apply H_absurd in H. contradiction. }
      specialize (t_composition t_composition_premise').
      clear t_composition_premise; clear t_composition_premise'.
      destruct t_composition as [t_comp1 t_comp2].
      apply t_comp2.
      exists (tc ++ [Ext (ExtRet r) ProgramOrigin]).
      exists ContextOrigin. reflexivity. }
    SCase "g1 = ✓".
    { (* We apply trace extensibility to A↓ *) 
      pose (trace_extensibility tc s g1 (COMPILE_PROG P↓)
        H_shp (COMPILE_PROG A↓) H_sha')
        as t_extensibility.
      destruct t_extensibility as [t_ext1 t_ext2].
      assert (in_Traces_a tc COMPILE_PROG A ↓ s /\
         in_Traces_p (tc ++ [Ext g1 ProgramOrigin])
         COMPILE_PROG P ↓ s) as H_conj.
      { split. apply H_def1. unfold tc.
        rewrite <- program_Ea_immuable_to_zeta.
        rewrite HD_g1. rewrite <- H_g1. apply H_zeta. }
      apply t_ext2 in H_conj.
      (* We apply trace composition *)
      pose (trace_composition (tc ++ Ea) s (COMPILE_PROG P↓)
        H_shp (COMPILE_PROG A↓) H_sha') as t_composition.
      assert (in_Traces_p (tc ++ Ea) COMPILE_PROG P ↓ s /\
        in_Traces_a (tc ++ Ea) COMPILE_PROG A ↓ s) as H_or.
      { split. unfold tc. rewrite H_g1.
        rewrite <- program_Ea_immuable_to_zeta.
        rewrite <- H_g1. apply H_zeta.
        rewrite H_g1. rewrite <- HD_g1. apply H_conj. }
      specialize (t_composition H_or); clear H_or.
      assert (forall (Ea0 : external_action) (o : origin),
        ~(in_Traces_p ((tc ++ Ea) ++ [Ext Ea0 o]) COMPILE_PROG P ↓ s /\
        in_Traces_a ((tc ++ Ea) ++ [Ext Ea0 o]) COMPILE_PROG A ↓ s))
        as H_premise.
      { intros. intro contra_assert. destruct contra_assert.
        rewrite H_g1 in H.
        pose (trace_post_terminaison 
          tc (Ext Ea0 o0) (COMPILE_PROG P↓) s ProgramOrigin)
          as H_absurd.
        rewrite app_assoc in H_absurd.
        apply H_absurd in H. contradiction. }
      specialize (t_composition H_premise); clear H_premise.
      destruct t_composition as [t_comp1 t_comp2].
      apply t_comp2. exists tc. exists ProgramOrigin.
      rewrite H_g1. reflexivity. }
  }
  (* Now we prove that A↓[Q↓] diverges *)
  assert (cprogram_diverges (LL_context_application
    (COMPILE_PROG A↓) (COMPILE_PROG Q↓))) as AQ_diverges.
  Case "that A↓[Q↓] diverges".
  { (* We deduce 3 things by canonicalization *)
    (* a *)
    assert (in_Traces_p tc (COMPILE_PROG Q↓) s) as canon_a.
    { unfold tc. apply canonicalization in H_tp2.
      apply H_tp2. apply WF_s. apply H_shQ. apply H_QFD. }
    (* b *)
    assert (in_Traces_p (zetaC_t (tp++[Ext End ProgramOrigin]))
     (COMPILE_PROG Q↓) s -> 
     in_Traces_p (tp++[Ext End ProgramOrigin]) (COMPILE_PROG Q↓) s)
     as canon_b.
    { intro. apply canonicalization in H. apply H.
      apply WF_s. apply H_shQ. apply H_QFD. }
    (* c *)
    assert (in_Traces_p (zetaC_t (tp++[Ext g1 ProgramOrigin]))
     (COMPILE_PROG Q↓) s -> 
     in_Traces_p (tp++[Ext g1 ProgramOrigin]) (COMPILE_PROG Q↓) s)
     as canon_c.
    { intro. apply canonicalization in H. apply H.
      apply WF_s. apply H_shQ. apply H_QFD. }
    (* We prove that Q↓ cannot perform (✓) *)
    assert (~(in_Traces_p (tc++[Ext ✓ ProgramOrigin])
      (COMPILE_PROG Q↓) s)) as cant_be_End.
    { intro contra. unfold tc in contra.
      rewrite <- program_Ea_immuable_to_zeta in contra.
      (* We use (b) *)
      apply canon_b in contra.
      (* We use trace extensibility *)
      pose (trace_extensibility tp s ✓ (COMPILE_PROG Q↓) 
        H_shq a H_sha) as t_extensibility.
      destruct t_extensibility as [t_ext1 t_ext2].
      assert (in_Traces_a tp a s /\ in_Traces_p 
        (tp ++ [Ext ✓ ProgramOrigin]) COMPILE_PROG Q ↓ s)
        as ext_premise.
      { split. destruct H_tp_in_Pa as [H_tp_in_Pa1 H_tp_in_Pa2].
        apply H_tp_in_Pa2. apply contra. }
      (* We use trace composition *)
      pose (trace_composition (tp ++ [Ext ✓ ProgramOrigin])
        s (COMPILE_PROG Q↓) H_shq a H_sha)
        as t_composition.
      assert (in_Traces_p (tp ++ [Ext ✓ ProgramOrigin])
        COMPILE_PROG Q ↓ s /\ in_Traces_a 
        (tp ++ [Ext ✓ ProgramOrigin]) a s) as ext_premise'.
      { split. apply contra. apply t_ext2.
        split. apply (trace_sets_closed_under_prefix_context
        tp ti a s H_sha H_tp1 H_tSets2). apply contra. }
      specialize (t_composition ext_premise').
      assert ((forall (Ea : external_action) (o : origin),
        ~(in_Traces_p ((tp ++ [Ext ✓ ProgramOrigin]) ++
        [Ext Ea o]) COMPILE_PROG Q ↓ s /\ in_Traces_a
        ((tp ++ [Ext ✓ ProgramOrigin]) ++ [Ext Ea o]) a s)))
        as ext_premise''.
      { intros. intro contra_assert. destruct contra_assert.
        pose (trace_post_terminaison 
          tp (Ext Ea0 o0) (COMPILE_PROG Q↓) s ProgramOrigin)
          as H_absurd.
        rewrite app_assoc in H_absurd.
        apply H_absurd in H. contradiction. }
      specialize (t_composition ext_premise'').
      destruct t_composition as [t_comp1 t_comp2].
      (* We state that Q↓ terminates which is a contradiction *)
      assert (cprogram_terminates
        (LL_context_application a COMPILE_PROG Q ↓)) as absurd.
      { apply t_comp2. exists tp. exists ProgramOrigin. trivial. }
      assert (cprogram_terminates
        (LL_context_application a COMPILE_PROG Q ↓) /\
        cprogram_diverges
        (LL_context_application a COMPILE_PROG Q ↓)) as absurd'.
      { split. apply absurd. apply aq_diverges. }
      apply LL_program_behavior_exclusion in absurd'.
      contradiction.
    }
    (* We prove that Q↓ cannot perform (g1) *)
    assert (~(in_Traces_p (tc++[Ext g1 ProgramOrigin])
      (COMPILE_PROG Q↓) s)) as cant_be_g1.
    { intro contra. unfold tc in contra.
      rewrite <- program_Ea_immuable_to_zeta in contra.
      apply canon_c in contra.
      pose (H_tp3' := H_tp3).
      specialize (H_tp3' (tp ++ [Ext g1 ProgramOrigin])).
      rewrite H_g1 in H_EaExists.
      specialize (H_tp3' (conj H_EaExists contra)).
      unfold is_a_prefix_of in H_tp3'. destruct H_tp3'.
      rewrite <- app_assoc in H.
      rewrite <- (app_nil_r tp) in H.
      assert ((tp ++ []) ++ [Ext g1 ProgramOrigin] ++ x
        = tp ++ [Ext g1 ProgramOrigin] ++ x) as H_a.
      { rewrite (app_nil_r tp). reflexivity. }
      rewrite H_a in H. clear H_a.
      apply app_inv_head in H. inversion H. }
    (* We have now two useful hypothesis *)
    (* Either Q↓ produces an external action or it doesn't *)
    (* We use the excluded middle law of classical logic *)
    pose (excluded_middle
      (forall g, ~in_Traces_p (tc++[Ext g ProgramOrigin])
      (COMPILE_PROG Q↓) s)) as EX1.
    destruct EX1 as [EX1 | EX1].
    SCase "No external action produced by Q↓".
    { pose (trace_composition tc s (COMPILE_PROG Q↓) H_shq
        (COMPILE_PROG A↓) H_sha') as t_composition.
      assert (in_Traces_p tc COMPILE_PROG Q ↓ s /\
        in_Traces_a tc COMPILE_PROG A ↓ s) as comp_premise.
      { split; assumption. }
      assert ((forall (Ea : external_action) (o : origin),
         ~(in_Traces_p (tc ++ [Ext Ea o]) COMPILE_PROG Q ↓ s /\
         in_Traces_a (tc ++ [Ext Ea o]) COMPILE_PROG A ↓ s)))
          as comp_premise'.
      { intros. intro contra. destruct contra. destruct o0.
        - admit.
        - apply (EX1 Ea0) in H. contradiction. }
      specialize (t_composition comp_premise comp_premise').
      destruct t_composition as [t_comp1 t_comp2].
      apply contrapositive in t_comp1.
      apply cterminates_cdiverges_opposition in t_comp1.
      apply t_comp1. intro contra.
      destruct contra as [t_contra contra].
      destruct contra as [o_contra contra].
      (* We can't have a terminating action *)
      admit.
    }
    SCase "External action performed by Q↓".
    { apply not_forall_dist in EX1.
      destruct EX1 as [g EX1].
      apply (double_negation_elimination 
        (in_Traces_p (tc ++ [Ext g ProgramOrigin])
          COMPILE_PROG Q ↓ s)) in EX1.
      (* Either the context produces an action or it doesn't *)
      pose (excluded_middle (forall g', ~in_Traces_p
        (tc++[Ext g ProgramOrigin]++[Ext g' ContextOrigin])
        (COMPILE_PROG A↓) s)) as EX2.
      destruct EX2 as [EX2 | EX2].
      SSCase "No external action produced by the context".
      { admit.
      }
      SSCase "External action procued by the context".
      { apply not_forall_dist in EX2.
        destruct EX2 as [g' EX2].
        apply (double_negation_elimination 
          (in_Traces_a (tc ++ [Ext g ProgramOrigin] ++
          [Ext g' ContextOrigin]) (COMPILE_PROG A↓) s)) in EX2.
        specialize (H_def3 g).
        (* g = g1 or g <> g1 *)
        pose (excluded_middle (g = g1)) as EX3.
        destruct EX3.
        SSSCase "g = g1".
        { rewrite H in EX1. apply cant_be_g1 in EX1. contradiction. }
        SSSCase "g <> g1".
        { assert (g = zeta_gamma g /\ g1 = zeta_gamma g1) as Ha.
          { admit. }
          destruct Ha. rewrite H0 in H; rewrite H1 in H.
          specialize (H_def3 H g').
          apply H_def3 in EX2. contradiction. }
      }
    }
  }
  exists A. intros. constructor. left. split.
  pose (separate_compilation_correctness_proof) as CompCorrectP.
  unfold separate_compilation_correctness in CompCorrectP.
  specialize (CompCorrectP s WF_s A P H_shA H_shP H_PFD H_AFD).
  destruct CompCorrectP.
  apply H0 in AP_terminates. apply AP_terminates.
  pose (separate_compilation_correctness_proof) as CompCorrectQ.
  unfold separate_compilation_correctness in CompCorrectQ.
  specialize (CompCorrectQ s WF_s A Q H_shA H_shQ H_QFD H_AFD).
  destruct CompCorrectQ.
  apply H1 in AQ_diverges. apply AQ_diverges.
Admitted.

Theorem structured_full_abstraction_proof :
  structured_full_abstraction.
Proof.
  unfold structured_full_abstraction.
  intros s WF_s P Q H_shP H_shQ H_PFD H_QFD.
  intro H_a. destruct H_a as [a [H_sha H_low_neq]].
  inversion H_low_neq as [ap aq H_behavior ap_eq aq_eq].
  destruct H_behavior as [H_behavior | H_behavior].
  - destruct H_behavior as [ap_terminates aq_diverges].
    pose (structured_full_abstraction_aux_proof a P Q
      s ap_terminates aq_diverges) as lemma.
    unfold structured_full_abstraction_aux in lemma.
    apply (lemma WF_s H_shP H_shQ H_PFD H_QFD (conj H_sha H_low_neq)).
  - destruct H_behavior as [ap_diverges aq_terminates].
    pose (structured_full_abstraction_aux_proof a Q P
      s aq_terminates ap_diverges) as lemma.
    unfold structured_full_abstraction_aux in lemma.
    specialize (lemma WF_s H_shQ H_shP H_QFD H_PFD).
    assert ((exists A : partial_program,
      CONTEXT_SHAPE A ∈∘ s /\ context_fully_defined s A ->
      HIGH_NEQ context_application A Q
      ≁H context_application A P)
        ->
    (exists A : partial_program,
      CONTEXT_SHAPE A ∈∘ s /\ context_fully_defined s A ->
      HIGH_NEQ context_application A P
      ≁H context_application A Q)) as H_assert.
    { intros HA. destruct HA as [A H].
      exists A. intros. apply H in H0.
      apply high_neq_symmetry. apply H0. }
    apply H_assert. apply lemma.
    split.
    + apply H_sha.
    + apply low_neq_symmetry. apply H_low_neq.
Qed. 

Definition secure_compartmentalizing_compilation : Prop :=
  admit.

Lemma SCC_isomorphism :
  structured_full_abstraction ->
  secure_compartmentalizing_compilation.
Proof.
Admitted.

Theorem SCCProof :
  secure_compartmentalizing_compilation.
Proof.
  apply SCC_isomorphism.
  apply structured_full_abstraction_proof.
Qed.

