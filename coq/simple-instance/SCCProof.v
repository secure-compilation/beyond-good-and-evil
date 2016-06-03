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

(* If a[P] ≁L a[Q] we say that a distinguish the partial
   programs P and Q. The same concept exists for ≁H *)

(* _____________________________________ 
           LEMMAS & PROPERTIES
   _____________________________________ *)

(* ------- Canonicalization ------- *)
Lemma canonicalization :
  forall t s,
  forall P, (PROGRAM_SHAPE P ∈• s) -> 
    (program_fully_defined s P) ->
    (in_Traces_p t (COMPILE_PROG P↓) s
      <-> 
     in_Traces_p (zetaC_t t) (COMPILE_PROG P↓) s).
Proof.
Admitted.

(* ------- Definability / Trace mappping algorithm ------- *)
Lemma definability :
  forall t g1 s, 
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

Definition structured_full_abstraction : Prop :=
  forall s,
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

Definition separate_compilation_correctness : Prop :=
  forall s,
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

Lemma trace_sets_closed_under_prefix_program :
  forall t' t p s, (LL_PROGRAM_SHAPE p ∈• s) ->
    incl t' t -> in_Traces_p t p s ->
    in_Traces_p t' p s.
Proof.
Admitted.

Lemma trace_sets_closed_under_prefix_context :
  forall t' t a s, (LL_CONTEXT_SHAPE a ∈∘ s) ->
    incl t' t -> in_Traces_a t a s ->
    in_Traces_p t' a s.
Proof.
Admitted.

Lemma LL_program_behavior_exclusion :
  forall p, cprogram_terminates p /\ cprogram_diverges p
    -> False.
Proof.
Admitted.

Lemma zetaC_t_idempotent :
  forall t, zetaC_t t = zetaC_t (zetaC_t t).
Proof.
Admitted.

Lemma program_Ea_immuable_to_zeta :
  forall t g1,
  zetaC_t (t ++ [Ext g1 ProgramOrigin])
  = zetaC_t (t) ++ [Ext g1 ProgramOrigin].
Proof.
Admitted.

Theorem structured_full_abstraction_proof :
  structured_full_abstraction.
Proof.
  unfold structured_full_abstraction.
  intros s.
  intros P Q H_shP H_shQ H_PFD H_QFD.
  (* We consider a ∈∘ s distinguishing P ∈• s and Q ∈• s *)
  intros H_a. destruct H_a as [a [H_sha H_low_neq]].
  inversion H_low_neq as [ap aq H_behavior ap_eq aq_eq].
  (* We suppose that a[P↓] terminates and a[Q↓] diverges *)
  destruct H_behavior as [H_behavior|H_behavior'].
  destruct H_behavior as [ap_terminates ap_diverges].
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
  assert 
    (exists tp, incl tp ti /\ 
      (in_Traces_p tp (COMPILE_PROG Q↓) s) /\
    (forall tp', (incl tp' ti) /\ 
      (in_Traces_p tp (COMPILE_PROG Q↓) s) ->
      (length tp') <= (length tp) 
    )) 
  as tp_exists.
  Case "Proof of existence of tp".
  { admit. }
  destruct tp_exists as [tp H_tp].
  destruct H_tp as [H_tp1 H_tp2].
  destruct H_tp2 as [H_tp2 H_tp3].
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
      tp ti a s H_sha H_tp1 H_tSets2).
  }
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
    { admit. }
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
    split. apply H_absurd. apply ap_diverges.
    apply (LL_program_behavior_exclusion
      (LL_context_application a COMPILE_PROG Q ↓)) in absurd.
    contradiction.
  }
  (* There exists Ea such that tp.Ea such that tp.Ea 
     is a prefix of ti *)
  assert (exists Ea, incl (tp++Ea) ti) as Ea_exists.
  { admit. }
  destruct Ea_exists as [Ea H_EaExists].
  (* Ea is a program action *)
  assert (exists g1, Ea = [Ext g1 ProgramOrigin])
    as H_program_action.
  { admit. }
  destruct H_program_action as [g1 H_g1].
  (* Let tc be the canonicalization of tp *)
  pose (tc := zetaC_t tp).
  (* tc is a trace of P↓ *)
  pose (canonicalization (tp++Ea) s P H_shP H_PFD)
    as H_canonicalization.
  destruct H_canonicalization as [H_canon1 H_canon2].
  assert (in_Traces_p (tp++Ea) (COMPILE_PROG P↓) s) as H_zeta.
  { admit. }
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
    exists (COMPILE_PROG P↓). intros H_def.
    unfold tc.
    rewrite <- (program_Ea_immuable_to_zeta tp g1).
    rewrite <- H_g1. apply H_zeta.
  }
  specialize (H_definability H_definability_premises).
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
        rewrite <- app_assoc. apply H_context_action.
      }
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
        rewrite <- app_assoc. apply H_context_action.
      }
      specialize (t_composition t_composition_premise).
      assert ((forall (Ea : external_action) (o : origin),
        ~(in_Traces_p (((tc ++ [Ext (ExtCall c p r) ProgramOrigin]) ++
          [Ext ✓ ContextOrigin]) ++ 
          [Ext Ea o]) COMPILE_PROG P ↓ s /\
        in_Traces_a (((tc ++ [Ext (ExtCall c p r) ProgramOrigin]) ++
          [Ext ✓ ContextOrigin]) ++ 
          [Ext Ea o]) COMPILE_PROG A ↓ s)))
        as t_composition_premise'.
      { admit. }
      specialize (t_composition t_composition_premise').
      clear t_composition_premise; clear t_composition_premise'.
      destruct t_composition as [t_comp1 t_comp2].
      apply t_comp2.
      exists (tc ++ [Ext (ExtCall c p r) ProgramOrigin]).
      exists ContextOrigin. reflexivity.
    }
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
        rewrite <- app_assoc. apply H_context_action.
      }
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
        rewrite <- app_assoc. apply H_context_action. 
      }
      specialize (t_composition t_composition_premise).
      assert ((forall (Ea : external_action) (o : origin),
        ~(in_Traces_p (((tc ++ [Ext (ExtRet r) ProgramOrigin]) ++
          [Ext ✓ ContextOrigin]) ++ 
          [Ext Ea o]) COMPILE_PROG P ↓ s /\
        in_Traces_a (((tc ++ [Ext (ExtRet r) ProgramOrigin]) ++
          [Ext ✓ ContextOrigin]) ++ 
          [Ext Ea o]) COMPILE_PROG A ↓ s)))
        as t_composition_premise'.
      { admit. }
      specialize (t_composition t_composition_premise').
      clear t_composition_premise; clear t_composition_premise'.
      destruct t_composition as [t_comp1 t_comp2].
      apply t_comp2.
      exists (tc ++ [Ext (ExtRet r) ProgramOrigin]).
      exists ContextOrigin. reflexivity.
    }
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
        rewrite HD_g1. rewrite <- H_g1. apply H_zeta.
      }
      apply t_ext2 in H_conj.
      (* We apply trace composition *)
      pose (trace_composition (tc ++ Ea) s (COMPILE_PROG P↓)
        H_shp (COMPILE_PROG A↓) H_sha') as t_composition.
      assert (in_Traces_p (tc ++ Ea) COMPILE_PROG P ↓ s /\
        in_Traces_a (tc ++ Ea) COMPILE_PROG A ↓ s) as H_or.
      { split. unfold tc. rewrite H_g1.
        rewrite <- program_Ea_immuable_to_zeta.
        rewrite <- H_g1. apply H_zeta.
        rewrite H_g1. rewrite <- HD_g1. apply H_conj.
      }
      specialize (t_composition H_or); clear H_or.
      assert (forall (Ea0 : external_action) (o : origin),
        ~(in_Traces_p ((tc ++ Ea) ++ [Ext Ea0 o]) COMPILE_PROG P ↓ s /\
        in_Traces_a ((tc ++ Ea) ++ [Ext Ea0 o]) COMPILE_PROG A ↓ s))
        as H_premise.
      { admit. }
      specialize (t_composition H_premise); clear H_premise.
      destruct t_composition as [t_comp1 t_comp2].
      apply t_comp2. exists tc. exists ProgramOrigin.
      rewrite H_g1. reflexivity.
    }
  }
  (* Now we prove that A↓[Q↓] diverges *)
  assert (cprogram_diverges (LL_context_application
    (COMPILE_PROG A↓) (COMPILE_PROG Q↓))) as AQ_terminates.
  Case "that A↓[Q↓] diverges".
  { (* We deduce 3 things by canonicalization *)
    (* a *)
    assert (in_Traces_p tc (COMPILE_PROG Q↓) s) as canon_a.
    { unfold tc. apply canonicalization in H_tp2.
      apply H_tp2. apply H_shQ. apply H_QFD.
    }
    (* b *)
    assert (in_Traces_p (zetaC_t (tp++[Ext End ProgramOrigin]))
     (COMPILE_PROG Q↓) s -> 
     in_Traces_p (tp++[Ext End ProgramOrigin]) (COMPILE_PROG Q↓) s)
     as canon_b.
    { intro. apply canonicalization in H. apply H.
      apply H_shQ. apply H_QFD.
    }
    (* c *)
    assert (in_Traces_p (zetaC_t (tp++[Ext g1 ProgramOrigin]))
     (COMPILE_PROG Q↓) s -> 
     in_Traces_p (tp++[Ext g1 ProgramOrigin]) (COMPILE_PROG Q↓) s)
     as canon_c.
    { intro. apply canonicalization in H. apply H.
      apply H_shQ. apply H_QFD.
    }
    (* Q↓ cannot perform (✓) nor (g1) nor any (γ?) *)
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
      { split. admit. admit.
      }
      admit.  
    }
    admit.
  }
  (* Symmetric case *)
  admit.
Admitted.

Definition secure_compartmentalizing_compilation : Prop :=
  admit.

Lemma SCC_isormorphism :
  structured_full_abstraction ->
  separate_compilation_correctness ->
  secure_compartmentalizing_compilation.
Proof.
Admitted.



