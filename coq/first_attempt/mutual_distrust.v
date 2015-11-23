Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Sorting.Permutation.

(* Let's define how to map a binary operator to a n-ary one. We define
   it as follows:
     nary_op [x1; ...; xn] =
       (...((x1 `op` x2) `op` x3) `op`  ... ) `op` xn
     nary_op [] = e

   The choice of e does not matter much; e is only present to fix a
   convention regarding what should happen when provided an empty
   list.
*)

Section BinaryToNary.
  
  Variables (T: Type) (op: T -> T -> T) (e: T).
  
  (* Main definition *)
  
  Definition nary: list T -> T :=
    fun xs =>
      match xs with
        | [] => e
        | x :: xs' => fold_left op xs' x
      end.

    (* Lemmas *)

    Lemma nary_append:
      forall (x: T) (xs ys: list T),
        nary ((x :: xs) ++ ys) = nary ((nary (x :: xs)) :: ys).
    Proof.
      intros x xs ys.
      unfold nary.
      now apply fold_left_app.
    Qed.

    Lemma nary_snoc:
      forall (x: T) (xs: list T) (y: T),
        nary ((x :: xs) ++ [y]) = op (nary (x :: xs)) y.
    Proof.
      intros x xs y.
      now apply (nary_append x xs [y]).
    Qed.
    
End BinaryToNary.

Arguments nary [_] _ _ _.
Arguments nary_append [_] _ _ _ _ _.
Arguments nary_snoc [_] _ _ _ _ _.

Section Replicate.

  Fixpoint replicate {T: Type} (n: nat) (x: T): list T :=
    match n with
      | 0 => []
      | S n' => x :: replicate n' x
    end.

  Lemma replicate_length:
    forall {T: Type} (n:nat) (x: T),
      length (replicate n x) = n.
  Proof.
    induction n; intro x; [now compute|].
    assert (replicate (S n) x = x :: replicate n x) as H
        by now compute.
    rewrite H.
    assert (length (x :: replicate n x) = S (length (replicate n x))) as H'
        by now compute.
    rewrite H'.
    rewrite (IHn x).
    reflexivity.
  Qed.

End Replicate.

(* Now we define a typeclass for compilers. It will be used *)
(* for specifying compilers in full abstraction settings as well as *)
(* mutual distrust settings. *)

Section Compiler.

  Class compiler (language: Type) (compilation_unit: language -> Set) :=
    Compiler {
        source: language;
        target: language;
        compile: compilation_unit source -> compilation_unit target
      }.

End Compiler.


(* Let's define what a language in a full abstraction setting looks *)
(* like, using a typeclass. We can then define full abstraction for a *)
(* compiler between such languages. *)

Section FullAbstraction.

  Class fa_language :=
    FALanguage {
        program: Set;
        context: Set;
        insert: context -> program -> program;
        beh_eq_prog: program -> program -> Prop;
        beh_eq_prog_refl: forall (P: program),
                            beh_eq_prog P P;
        beh_eq_prog_trans: forall (P Q R: program),
                             beh_eq_prog P Q ->
                             beh_eq_prog Q R ->
                             beh_eq_prog P R;
        beh_eq_prog_sym: forall (P Q: program),
                           beh_eq_prog P Q -> beh_eq_prog Q P
      }.

  Definition fa_compiler := compiler fa_language (@program).

  Let fa_ctx_eq {L: fa_language} (P Q: program): Prop :=
    forall (A: context),
      beh_eq_prog (insert A P) (insert A Q).

  Definition full_abstraction (compiler: fa_compiler): Prop :=
    forall (P Q : @program (@source _ _ compiler)),
      fa_ctx_eq P Q <-> fa_ctx_eq (compile P) (compile Q).

End FullAbstraction.


(* Let's define what a language in a mutual distrust setting looks *)
(* like, using a typeclass. We can then define mutual distrust for a *)
(* compiler between such languages. *)

Section MutualDistrust.

  Class md_language :=
    MDLanguage {
        component: Set;
        empty: component;
        link: component -> component -> component;
        beh_eq_comp: component -> component -> Prop;
        empty_neutral_left: forall (P: component),
                              beh_eq_comp P (link empty P);
        link_permutation: forall (Ps: list component) (Qs: list component),
                            Permutation Ps Qs ->
                            beh_eq_comp (nary link empty Ps)
                                        (nary link empty Qs);
        beh_eq_comp_refl: forall (P: component),
                            beh_eq_comp P P;
        beh_eq_comp_trans: forall (P Q R: component),
                             beh_eq_comp P Q ->
                             beh_eq_comp Q R ->
                             beh_eq_comp P R;
        beh_eq_comp_sym: forall (P Q: component),
                           beh_eq_comp P Q -> beh_eq_comp Q P
      }.

  Definition md_compiler :=
    compiler md_language (@component).

  Let md_ctx_eq {L: md_language} (n_ctx: nat)
      (P: component) (Ps: list component)
      (Q: component) (Qs: list component): Prop :=
    forall As: list component,
      length As = n_ctx ->
      beh_eq_comp (nary link empty ((P :: Ps) ++ As))
                  (nary link empty ((Q :: Qs) ++ As)).

  Definition mutual_distrust (compiler: md_compiler): Prop :=
    let source_component := @component (@source _ _ compiler) in
    forall (n_att n_prog: nat),
      forall (P: source_component) (Ps: list source_component)
             (Q: source_component) (Qs: list source_component),
        length (P :: Ps) = n_prog ->
        length (Q :: Qs) = n_prog ->
        (md_ctx_eq n_att P Ps Q Qs
         <->
         md_ctx_eq n_att (compile P) (map compile Ps)
                   (compile Q) (map compile Qs)).

End MutualDistrust.


(* Now, starting from a compiler for a mutual distrust setting, we *)
(* recover the full abstraction setting by equating components with *)
(* programs and contexts. We show that full abstraction implies mutual *)
(* distrust in this case, assuming correct and separate *)
(* compilation lemmas. *)

Section FullAbstractionImpliesMutualDistrust.

  Variable C: md_compiler.

  Let src: md_language := @source _ _ C.
  Let tgt: md_language := @target _ _ C.

  Let fa_ctx_eq {L: md_language} (P Q: component): Prop :=
    forall (A: component),
      beh_eq_comp (link A P) (link A Q).

  Let md_ctx_eq {L: md_language} (n_ctx: nat)
      (P: component) (Ps: list component)
      (Q: component) (Qs: list component): Prop :=
    forall As: list component,
      length As = n_ctx ->
      beh_eq_comp (nary link empty ((P :: Ps) ++ As))
                  (nary link empty ((Q :: Qs) ++ As)).

  (* (only) required for the case where nothing is compromised *)
  Hypothesis (correct_compilation:
                forall (P Q: @component src),
                  beh_eq_comp P Q <-> beh_eq_comp (compile P) (compile Q)).

  Hypothesis (separate_compilation:
                forall (Ps: list (@component src)),
                  fa_ctx_eq (compile (nary link empty Ps))
                            (nary link empty (map compile Ps))).

  
  (* Lemmas about usual contextual equivalence. *)

  Lemma fa_ctx_eq_implies_beh_eq {L: md_language}:
    forall (P Q: component), fa_ctx_eq P Q -> beh_eq_comp P Q.
  Proof.
    intros P Q H.
    pose (H empty) as H'.
    pose (empty_neutral_left P) as HemptyP.
    pose (empty_neutral_left Q) as HemptyQ.
    apply (beh_eq_comp_trans _ (link empty Q) _).
    + now apply (beh_eq_comp_trans _ (link empty P) _).
    + now apply beh_eq_comp_sym.
  Qed.

  Lemma fa_ctx_eq_refl {L: md_language}:
    forall (P: component), fa_ctx_eq P P.
  Proof.
    intros P A.
    apply beh_eq_comp_refl.
  Qed.

  Lemma fa_ctx_eq_trans {L: md_language}:
    forall (P Q R: component),
      fa_ctx_eq P Q -> fa_ctx_eq Q R -> fa_ctx_eq P R.
  Proof.
    intros P Q R HPQ HQR A.
    apply (beh_eq_comp_trans _ (link A Q) _); [
        apply HPQ | apply HQR
      ].
  Qed.

  Lemma fa_ctx_eq_sym {L: md_language}:
    forall (P Q: component), fa_ctx_eq P Q -> fa_ctx_eq Q P.
  Proof.
    intros P Q HPQ A.
    apply beh_eq_comp_sym.
    apply HPQ.
  Qed.

  (* Lemmas about linking. *)

  Lemma link_comm {L: md_language}:
    forall (P Q: component), beh_eq_comp (link P Q) (link Q P).
  Proof.
    intros P Q.
    pose [P] as Ps.
    pose [Q] as Qs.
    pose (Ps ++ Qs) as PQ.
    pose (Qs ++ Ps) as QP.
    assert (Permutation PQ QP) as HPQQP.
    { now apply Permutation_app_comm. }
    pose (link_permutation PQ QP HPQQP) as H.
    now compute in H.
  Qed.

  Lemma empty_neutral_right {L: md_language}:
    forall (P: component), beh_eq_comp P (link P empty).
  Proof.
    intro P.
    apply (beh_eq_comp_trans _ (link empty P) _).
    + now apply empty_neutral_left.
    + now apply link_comm.
  Qed.

  Lemma link_app {L: md_language}:
    forall (P: component) (Ps: list component) (Q: component) (Qs: list component),
      beh_eq_comp
        (link (nary link empty (P :: Ps)) (nary link empty (Q :: Qs)))
        (nary link empty ((P :: Ps) ++ (Q :: Qs))).
  Proof.
    intros P Ps Q Qs.
    rewrite <- (nary_snoc link empty P Ps (nary link empty (Q :: Qs))).
    apply (beh_eq_comp_trans
             _ (nary link empty ([nary link empty (Q :: Qs)] ++ (P :: Ps))) _).
    { apply link_permutation.
      now apply Permutation_app_comm. }
    assert ([nary link empty (Q :: Qs)] ++ (P :: Ps) =
            nary link empty (Q :: Qs) :: P :: Ps) as H
        by now compute.
    rewrite H.
    rewrite <- (nary_append link empty Q Qs (P :: Ps)).
    apply link_permutation.
    now apply Permutation_app_comm.
  Qed.

  Lemma nary_link_empty {L: md_language}:
    forall (n: nat) (Ps: list component),
      beh_eq_comp (nary link empty (Ps ++ (replicate n empty)))
                  (nary link empty Ps).
  Proof.
    intro n.
    induction n.
    + intro Ps.
      unfold replicate.
      rewrite (app_nil_r Ps).
      now apply beh_eq_comp_refl.
    + intro Ps.
      assert (replicate (S n) empty = empty :: replicate n empty) as H
          by now unfold replicate.
      rewrite H.
      assert (empty :: replicate n empty = [empty] ++ replicate n empty)
        as H'
          by now compute.
      rewrite H'.
      assert (Ps ++ ([empty] ++ replicate n empty)
              = (Ps ++ [empty]) ++ (replicate n empty))
        as H''
          by now apply app_assoc.
      rewrite H''.
      apply (beh_eq_comp_trans _ (nary link empty (Ps ++ [empty])) _).
      * now apply (IHn (Ps ++ [empty])).
      * destruct Ps as [|P Ps']; [now apply beh_eq_comp_refl|].
        assert (nary link empty ((P :: Ps') ++ [empty]) = link (nary link empty (P :: Ps')) empty) as H'''
          by now apply nary_snoc.
        rewrite H'''.
        apply beh_eq_comp_sym.
        now apply empty_neutral_right.
  Qed.

  (* Key lemmas. *)

  Lemma fa_ctx_eq_implies_nz_md_ctx_eq {L: md_language}:
    forall (n: nat)
           (P: component) (Ps: list component)
           (Q: component) (Qs: list component),
      fa_ctx_eq (nary link empty (P :: Ps)) (nary link empty (Q :: Qs)) ->
      md_ctx_eq (S n) P Ps Q Qs.
  Proof.
    pose (nary_append link empty) as Hlink.
    intros n P Ps Q Qs H.
    intros As HAs.
    destruct As as [|A0 As']; [now exfalso|].
    rewrite (Hlink P Ps (A0 :: As')).
    rewrite (Hlink Q Qs (A0 :: As')).
    pose (A0 :: As') as As.
    pose (H (nary link empty As)) as HA0.
    assert (beh_eq_comp (nary link empty (As ++ (P :: Ps)))
                        (nary link empty (As ++ (Q :: Qs)))) as HA1.
    { apply (beh_eq_comp_trans
               _ (link (nary link empty As)
                       (nary link empty (P :: Ps))) _).
      + apply beh_eq_comp_sym; now apply link_app.
      + apply (beh_eq_comp_trans
                 _ (link (nary link empty As)
                         (nary link empty (Q :: Qs))) _).
        * assumption.
        * now apply link_app. }
    assert (beh_eq_comp (nary link empty ((P :: Ps) ++ As))
                        (nary link empty ((Q :: Qs) ++ As))) as HA2.
    { apply (beh_eq_comp_trans _ (nary link empty (As ++ (P :: Ps))) _).
      + apply beh_eq_comp_sym.
        apply link_permutation.
        now apply Permutation_app_comm.
      + apply (beh_eq_comp_trans _ (nary link empty (As ++ (Q :: Qs))) _).
        * assumption.
        * apply link_permutation.
          now apply Permutation_app_comm. }
    rewrite (Hlink P Ps As) in HA2.
    now rewrite (Hlink Q Qs As) in HA2.
  Qed.

  Lemma nz_md_ctx_eq_implies_fa_ctx_eq {L: md_language}:
    forall (n: nat)
           (P: component) (Ps: list component)
           (Q: component) (Qs: list component),
      md_ctx_eq (S n) P Ps Q Qs ->
      fa_ctx_eq (nary link empty (P :: Ps)) (nary link empty (Q :: Qs)).
  Proof.
    intros n P Ps Q Qs H A.
    pose (A :: (replicate n empty)) as As.
    assert (length As = S (length (replicate n empty)))
      as HAs by (unfold As; now unfold length).
    rewrite (replicate_length n empty) in HAs.
    pose (H As HAs) as H0.
    assert ((P :: Ps) ++ As = (P :: Ps) ++ ([A] ++ replicate n empty)) as H'Ps
        by (unfold As; now unfold app).
    rewrite H'Ps in H0.
    assert ((P :: Ps) ++ ([A] ++ replicate n empty) =
            ((P :: Ps) ++ [A]) ++ (replicate n empty)) as H''Ps
        by now apply app_assoc.
    rewrite H''Ps in H0.
    assert ((Q :: Qs) ++ As = (Q :: Qs) ++ ([A] ++ replicate n empty)) as H'Qs
        by now unfold As.
    rewrite H'Qs in H0.
    assert ((Q :: Qs) ++ ([A] ++ replicate n empty) =
            ((Q :: Qs) ++ [A]) ++ (replicate n empty)) as H''Qs
        by now apply app_assoc.
    rewrite H''Qs in H0.
    assert (beh_eq_comp
              (nary link empty ((P :: Ps) ++ [A]))
              (nary link empty ((Q :: Qs) ++ [A]))
           ) as H1.
    { apply (beh_eq_comp_trans
               _ (nary link empty (((P :: Ps) ++ [A]) ++ (replicate n empty))) _).
      + apply beh_eq_comp_sym.
        now apply nary_link_empty.
      + apply (beh_eq_comp_trans
                 _ (nary link empty (((Q :: Qs) ++ [A]) ++ (replicate n empty))) _).
        * assumption.
        * now apply nary_link_empty. }
    rewrite (nary_snoc link empty P Ps A) in H1.
    rewrite (nary_snoc link empty Q Qs A) in H1.
    apply (beh_eq_comp_trans _ (link (nary link empty (P :: Ps)) A) _).
    + apply beh_eq_comp_sym.
      now apply link_comm.
    + apply (beh_eq_comp_trans _ (link (nary link empty (Q :: Qs)) A) _).
      * assumption.
      * now apply link_comm.
  Qed.

  Lemma z_md_ctx_eq_beh_eq_comp {L: md_language}:
    forall (P: component) (Ps: list component)
           (Q: component) (Qs: list component),
      md_ctx_eq 0 P Ps Q Qs
      <->
      beh_eq_comp (nary link empty (P :: Ps)) (nary link empty (Q :: Qs)).
  Proof.
    intros P Ps Q Qs.
    split; intro H.
    + pose (H [] (eq_refl (length []))) as H'.
      rewrite (app_nil_r (P :: Ps)) in H'.
      now rewrite (app_nil_r (Q :: Qs)) in H'.
    + intros As HAs.
      assert (As = []) as HnilAs
          by (destruct As; [reflexivity | compute in HAs; now exfalso]).
      rewrite HnilAs.
      rewrite (app_nil_r (P :: Ps)).
      now rewrite (app_nil_r (Q :: Qs)).
  Qed.

  Lemma z_md:
    forall (P: @component src) (Ps: list (@component src))
           (Q: @component src) (Qs: list (@component src)),
      md_ctx_eq 0 P Ps Q Qs
      <->
      md_ctx_eq 0 (compile P) (map compile Ps) (compile Q) (map compile Qs).
  Proof.
    intros P Ps Q Qs.
    split.
    + intro H0.
      assert (beh_eq_comp (nary link empty (P :: Ps))
                          (nary link empty (Q :: Qs))) as H1
          by now apply z_md_ctx_eq_beh_eq_comp.
      assert (beh_eq_comp (compile (nary link empty (P :: Ps)))
                          (compile (nary link empty (Q :: Qs)))) as H2
          by now apply correct_compilation.
      assert (beh_eq_comp (nary link empty (map compile (P :: Ps)))
                          (nary link empty (map compile (Q :: Qs)))) as H3.
      { apply (beh_eq_comp_trans _ (compile (nary link empty (P :: Ps))) _).
        + apply beh_eq_comp_sym.
          apply fa_ctx_eq_implies_beh_eq.
          now apply separate_compilation.
        + apply (beh_eq_comp_trans _ (compile (nary link empty (Q :: Qs))) _).
          * assumption.
          * apply fa_ctx_eq_implies_beh_eq.
            now apply separate_compilation. }
      now apply z_md_ctx_eq_beh_eq_comp.
    + intro H4.
      assert (beh_eq_comp (nary link empty (map compile (P :: Ps)))
                          (nary link empty (map compile (Q :: Qs)))) as H3
          by now apply z_md_ctx_eq_beh_eq_comp.
      assert (beh_eq_comp (compile (nary link empty (P :: Ps)))
                          (compile (nary link empty (Q :: Qs)))) as H2.
      { apply (beh_eq_comp_trans _ (nary link empty (map compile (P :: Ps))) _).
        + apply fa_ctx_eq_implies_beh_eq.
          now apply separate_compilation.
        + apply (beh_eq_comp_trans _ (nary link empty (map compile (Q :: Qs))) _).
          * assumption.
          * apply beh_eq_comp_sym.
            apply fa_ctx_eq_implies_beh_eq.
            now apply separate_compilation. }
      assert (beh_eq_comp (nary link empty (P :: Ps)) (nary link empty (Q :: Qs))) as H1
          by now apply correct_compilation.
      now apply z_md_ctx_eq_beh_eq_comp.
  Qed.


  (* Theorem. *)

  Let src': fa_language :=
    {| program := @component src;
       context := @component src;
       insert := link;
       beh_eq_prog := beh_eq_comp;
       beh_eq_prog_refl := beh_eq_comp_refl;
       beh_eq_prog_trans := beh_eq_comp_trans;
       beh_eq_prog_sym := beh_eq_comp_sym
    |}.

  Let tgt': fa_language :=
    {| program := @component tgt;
       context := @component tgt;
       insert := link;
       beh_eq_prog := beh_eq_comp;
       beh_eq_prog_refl := beh_eq_comp_refl;
       beh_eq_prog_trans := beh_eq_comp_trans;
       beh_eq_prog_sym := beh_eq_comp_sym
    |}.

  Let C': compiler fa_language (@program) :=
    {| source := src';
       target := tgt';
       compile := @compile _ _ C
    |}.

  Theorem fa_implies_md:
    full_abstraction C' -> mutual_distrust C.
  Proof.
    intro FA.
    unfold mutual_distrust.
    intros n_att n_prog P Ps Q Qs HnPs HnQs.
    destruct (FA (nary link empty (P :: Ps)) (nary link empty (Q :: Qs))) as [FA' FA''].
    destruct n_att as [|n_att'].
    + exact (z_md P Ps Q Qs).
    + pose (S n_att') as n_att.
      split.
      * intro H.
        assert (md_ctx_eq n_att P Ps Q Qs) as Hmd_ctx_eq_src
            by exact H.
        assert (fa_ctx_eq (nary link empty (P :: Ps)) (nary link empty (Q :: Qs))) as Hfa_ctx_eq_src
            by now apply (nz_md_ctx_eq_implies_fa_ctx_eq n_att').
        assert (fa_ctx_eq (compile (nary link empty (P :: Ps))) (compile (nary link empty (Q :: Qs))))
          as Hfa_ctx_eq_tgt
            by (unfold fa_ctx_eq; now apply FA').
        assert (fa_ctx_eq (nary link empty (map compile (P :: Ps)))
                          (nary link empty (map compile (Q :: Qs))))
          as Hfa_ctx_eq_tgt'.
        { apply (fa_ctx_eq_trans _ (compile (nary link empty (P :: Ps))) _).
          + apply fa_ctx_eq_sym.
            now apply separate_compilation.
          + apply (fa_ctx_eq_trans _ (compile (nary link empty (Q :: Qs))) _).
            * assumption.
            * now apply separate_compilation. }
        assert (md_ctx_eq n_att (compile P) (map compile Ps)
                                (compile Q) (map compile Qs))
          as Hmd_ctx_eq_tgt
            by now apply (fa_ctx_eq_implies_nz_md_ctx_eq n_att').
        exact Hmd_ctx_eq_tgt.
      * intro H.
        assert (md_ctx_eq n_att (compile P) (map compile Ps)
                                (compile Q) (map compile Qs))
          as Hmd_ctx_eq_tgt
            by exact H.
        assert (fa_ctx_eq (nary link empty (map compile (P :: Ps)))
                          (nary link empty (map compile (Q :: Qs))))
          as Hfa_ctx_eq_tgt
            by now apply (nz_md_ctx_eq_implies_fa_ctx_eq n_att').
        assert (fa_ctx_eq (compile (nary link empty (P :: Ps))) (compile (nary link empty (Q :: Qs))))
          as Hfa_ctx_eq_tgt'.
        { apply (fa_ctx_eq_trans _ (nary link empty (map compile (P :: Ps))) _).
          + now apply separate_compilation.
          + apply (fa_ctx_eq_trans _ (nary link empty (map compile (Q :: Qs))) _).
            * assumption.
            * apply fa_ctx_eq_sym.
              now apply separate_compilation. }
        assert (fa_ctx_eq (nary link empty (P :: Ps)) (nary link empty (Q :: Qs))) as Hfa_ctx_eq_src
            by (unfold fa_ctx_eq; now apply FA'').
        assert (md_ctx_eq n_att P Ps Q Qs) as Hmd_ctx_eq_src
            by now apply (fa_ctx_eq_implies_nz_md_ctx_eq n_att').
        exact Hmd_ctx_eq_src.
  Qed.

End FullAbstractionImpliesMutualDistrust.
