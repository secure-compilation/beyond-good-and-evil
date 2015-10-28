Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Sorting.Permutation.

(* First we define a type for non-empty lists together with some *)
(* lemmas about it. This is useful to define a n-ary operator out of *)
(* a 2-ary operation, without having to take care of the empty *)
(* list. *)

Section NonEmptyList.

  (* Main definitions *)

  Inductive nelist (T: Type): Type :=
  | nelist_cons: T -> list T -> nelist T.

  Arguments nelist_cons [_] _ _.

  Definition nary {T: Type} (op: T -> T -> T): nelist T -> T :=
    fun xs =>
      match xs with
        | nelist_cons x xs' => fold_left op xs' x
      end.


  (* Auxiliary functions *)

  Fixpoint nelist_to_list {T: Type} (xs: nelist T): list T :=
    match xs with
      | nelist_cons x xs' => x :: xs'
    end.

  Definition nelist_concat_list {T: Type} (xs: nelist T) (ys: list T): nelist T :=
    match xs with
      | nelist_cons x xs' => nelist_cons x (xs' ++ ys)
    end.

  Definition list_concat_nelist {T: Type} (xs: list T) (ys: nelist T): nelist T :=
    match xs with
      | [] => ys
      | x :: xs' => nelist_cons x (xs' ++ nelist_to_list ys)
    end.

    Definition nelist_concat_nelist {T: Type} (xs: nelist T) (ys: nelist T): nelist T :=
      nelist_concat_list xs (nelist_to_list ys).

    Definition nelist_length {T: Type} (xs: nelist T): nat :=
      length (nelist_to_list xs).

    Definition nelist_map {A B: Type} (f: A -> B) (xs: nelist A): nelist B :=
      match xs with
        | nelist_cons x xs' => nelist_cons (f x) (map f xs')
      end.

    Definition nelist_permutation {T: Type} (xs ys: nelist T) :=
      Permutation (nelist_to_list xs) (nelist_to_list ys).


    (* Lemmas about concatenation *)

    Lemma nelist_concat_nil {T: Type}:
      forall (xs: nelist T), nelist_concat_list xs [] = xs.
    Proof.
      intro xs.
      unfold nelist_concat_list.
      destruct xs as [x xs'].
      assert (xs' ++ [] = xs') as H by apply app_nil_r.
      now rewrite H.
    Qed.

    Lemma nelist_concat_list_to_list {T: Type}:
      forall (xs: nelist T) (ys: list T),
        nelist_to_list (nelist_concat_list xs ys) = (nelist_to_list xs) ++ ys.
    Proof.
      intros xs ys.
      destruct xs as [x xs'].
      unfold nelist_concat_list.
      unfold nelist_to_list.
      now apply app_comm_cons.
    Qed.

    Lemma nelist_concat_nelist_to_list {T: Type}:
      forall (xs ys: nelist T),
        nelist_to_list (nelist_concat_nelist xs ys) = (nelist_to_list xs) ++ (nelist_to_list ys).
    Proof.
      intros xs ys.
      unfold nelist_concat_nelist.
      now apply nelist_concat_list_to_list.
    Qed.

    Lemma nelist_concat_nelist_permutation {T: Type}:
      forall (xs ys: nelist T),
        nelist_permutation (nelist_concat_nelist xs ys) (nelist_concat_nelist ys xs).
    Proof.
      intros xs ys.
      unfold nelist_permutation.
      rewrite (nelist_concat_nelist_to_list xs ys).
      rewrite (nelist_concat_nelist_to_list ys xs).
      now apply Permutation_app_comm.
    Qed.

    Lemma nelist_concat_nelist_nelist_concat_list {T: Type}:
      forall (xs: nelist T) (y: T) (ys': list T),
        nelist_concat_nelist xs (nelist_cons y ys') = nelist_concat_list xs (y :: ys').
    Proof.
      intros xs y ys.
      unfold nelist_concat_nelist.
      now compute.
    Qed.


    (* Lemmas about nary *)

    Lemma nary_nelist_concat_list {T: Type}:
      forall (op: T -> T -> T) (xs: nelist T) (ys: list T),
        nary op (nelist_concat_list xs ys)
        = nary op (nelist_cons (nary op xs) ys).
    Proof.
      intros op xs ys.
      destruct xs as [x xs'].
      unfold nelist_concat_list.
      unfold nary.
      now apply fold_left_app.
    Qed.

    Lemma nary_nelist_concat_nelist {T: Type}:
      forall (op: T -> T -> T) (xs ys: nelist T),
        nary op (nelist_concat_nelist xs ys)
        = nary op (nelist_cons (nary op xs) (nelist_to_list ys)).
    Proof.
      intros op xs ys.
      unfold nelist_concat_nelist.
      now apply nary_nelist_concat_list.
    Qed.

    Lemma nary_nelist_snoc {T: Type}:
      forall (op: T -> T -> T) (xs: nelist T) (y: T),
        nary op (nelist_concat_nelist xs (nelist_cons y []))
        = op (nary op xs) y.
    Proof.
      intros op xs y.
      now apply (nary_nelist_concat_nelist op xs (nelist_cons y [])).
    Qed.

End NonEmptyList.


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
                             beh_eq_prog P Q -> beh_eq_prog Q R -> beh_eq_prog P R;
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
        link_permutation: forall (Ps Qs: nelist component),
                            nelist_permutation Ps Qs ->
                            beh_eq_comp (nary link Ps) (nary link Qs);
        beh_eq_comp_refl: forall (P: component),
                            beh_eq_comp P P;
        beh_eq_comp_trans: forall (P Q R: component),
                             beh_eq_comp P Q -> beh_eq_comp Q R -> beh_eq_comp P R;
        beh_eq_comp_sym: forall (P Q: component),
                           beh_eq_comp P Q -> beh_eq_comp Q P
      }.

  Definition md_compiler :=
    compiler md_language (@component).

  Let md_ctx_eq {L: md_language} (n_ctx: nat) (Ps Qs: nelist component): Prop :=
    forall As: list component, length As = n_ctx ->
    beh_eq_comp (nary link (nelist_concat_list Ps As)) (nary link (nelist_concat_list Qs As)).

  Definition mutual_distrust (compiler: md_compiler): Prop :=
    forall (n n_att n_prog: nat), n = n_att + n_prog ->
    forall (Ps Qs: nelist (@component (@source _ _ compiler))),
      nelist_length Ps = n_prog -> nelist_length Qs = n_prog ->
      (md_ctx_eq n_att Ps Qs
       <->
       md_ctx_eq n_att (nelist_map compile Ps) (nelist_map compile Qs)).

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

  Let md_ctx_eq {L: md_language} (n_ctx: nat) (Ps Qs: nelist component): Prop :=
    forall As: list component, length As = n_ctx ->
    beh_eq_comp (nary link (nelist_concat_list Ps As)) (nary link (nelist_concat_list Qs As)).

  (* (only) required for the case where nothing is compromised *)
  Hypothesis (correct_compilation:
                forall (P Q: @component src),
                  beh_eq_comp P Q <-> beh_eq_comp (compile P) (compile Q)).

  Hypothesis (separate_compilation:
                forall (Ps: nelist (@component src)),
                  fa_ctx_eq (compile (nary link Ps))
                            (nary link (nelist_map compile Ps))).


  (* Auxiliary definitions *)

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


  (* Lemmas about usual contextual equivalence. *)

  Lemma fa_ctx_eq_implies_beh_eq {L: md_language}:
    forall (P Q: component), fa_ctx_eq P Q -> beh_eq_comp P Q.
  Proof.
    intros P Q H.
    pose (H empty) as H'.
    pose (empty_neutral_left P) as HemptyP.
    pose (empty_neutral_left Q) as HemptyQ.
    apply (beh_eq_comp_trans _ (link empty Q) _).
      apply (beh_eq_comp_trans _ (link empty P) _).
        assumption.
      assumption.
    apply beh_eq_comp_sym.
    apply HemptyQ.
  Qed.

  Lemma fa_ctx_eq_refl {L: md_language}:
    forall (P: component), fa_ctx_eq P P.
  Proof.
    intros P A.
    apply beh_eq_comp_refl.
  Qed.

  Lemma fa_ctx_eq_trans {L: md_language}:
    forall (P Q R: component), fa_ctx_eq P Q -> fa_ctx_eq Q R ->
                               fa_ctx_eq P R.
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
    pose (nelist_cons _ P []) as Ps.
    pose (nelist_cons _ Q []) as Qs.
    pose (nelist_concat_nelist Ps Qs) as PQ.
    pose (nelist_concat_nelist Qs Ps) as QP.
    assert (nelist_permutation PQ QP) as HPQQP
      by apply nelist_concat_nelist_permutation.
    pose (link_permutation PQ QP HPQQP) as H.
    now compute in H.
  Qed.

  Lemma empty_neutral_right {L: md_language}:
    forall (P: component), beh_eq_comp P (link P empty).
  Proof.
    intro P.
    apply (beh_eq_comp_trans _ (link empty P) _); [
        now apply empty_neutral_left
      | now apply link_comm
      ].
  Qed.

  Lemma link_nelist_concat_nelist {L: md_language}:
    forall (Ps Qs: nelist component),
      beh_eq_comp
        (link (nary link Ps) (nary link Qs))
        (nary link (nelist_concat_nelist Ps Qs)).
  Proof.
    intros Ps Qs.
    rewrite <- (nary_nelist_snoc link Ps (nary link Qs)).
    apply (beh_eq_comp_trans
             _ (nary link (nelist_concat_nelist (nelist_cons component (nary link Qs) []) Ps)) _); [
        apply link_permutation; now apply nelist_concat_nelist_permutation
       |].
    assert (nelist_concat_nelist (nelist_cons component (nary link Qs) []) Ps
            = nelist_cons component (nary link Qs) (nelist_to_list Ps)) as H
        by (unfold nelist_concat_nelist; unfold nelist_concat_list; now rewrite app_nil_l).
    rewrite H.
    rewrite <- (nary_nelist_concat_nelist link Qs Ps).
    apply link_permutation.
    now apply nelist_concat_nelist_permutation.
  Qed.

  Lemma nary_link_empty {L: md_language}:
    forall (n: nat) (Ps: nelist component),
      beh_eq_comp (nary link (nelist_concat_list Ps (replicate n empty)))
                  (nary link Ps).
  Proof.
    intro n.
    induction n.
    + intro Ps.
      destruct Ps as [P Ps'].
      unfold replicate.
      unfold nelist_concat_list.
      rewrite (app_nil_r Ps').
      now apply beh_eq_comp_refl.
    + intro Ps.
      assert (replicate (S n) empty = empty :: replicate n empty) as H
          by now unfold replicate.
      rewrite H.
      assert (empty :: replicate n empty = [empty] ++ replicate n empty)
        as H'
          by now compute.
      rewrite H'.
      assert (nelist_concat_list Ps ([empty] ++ replicate n empty)
              = nelist_concat_list (nelist_concat_list Ps [empty]) (replicate n empty))
        as H''
          by (destruct Ps as [P Ps'];
              unfold nelist_concat_list;
              now rewrite app_assoc).
      rewrite H''.
      apply (beh_eq_comp_trans _ (nary link (nelist_concat_list Ps [empty])) _).
      * now apply (IHn (nelist_concat_list Ps [empty])).
      * assert (nary link (nelist_concat_list Ps [empty]) = link (nary link Ps) empty) as H'''
          by now apply nary_nelist_snoc.
        rewrite H'''.
        apply beh_eq_comp_sym.
        now apply empty_neutral_right.
  Qed.


  (* Key lemmas. *)

  Lemma fa_ctx_eq_implies_nz_md_ctx_eq {L: md_language}:
    forall (n: nat) (Ps Qs: nelist component),
      fa_ctx_eq (nary link Ps) (nary link Qs) ->
      md_ctx_eq (S n) Ps Qs.
  Proof.
    pose (nary_nelist_concat_list link) as Hlink.
    intros n Ps Qs H.
    intros As HAs.
    destruct As as [|A0 As']; [now exfalso|].
    rewrite (Hlink Ps (A0 :: As')).
    rewrite (Hlink Qs (A0 :: As')).
    pose (nelist_cons _ A0 As') as As.
    pose (H (nary link As)) as HA0.
    assert (beh_eq_comp (nary link (nelist_concat_nelist As Ps))
                        (nary link (nelist_concat_nelist As Qs))) as HA1
        by (apply (beh_eq_comp_trans _ (link (nary link As) (nary link Ps)) _); [
              apply beh_eq_comp_sym; now apply link_nelist_concat_nelist
            | apply (beh_eq_comp_trans _ (link (nary link As) (nary link Qs)) _); [
                assumption | now apply link_nelist_concat_nelist
              ]
            ]).
    assert (beh_eq_comp (nary link (nelist_concat_nelist Ps As))
                        (nary link (nelist_concat_nelist Qs As))) as HA2
        by (apply (beh_eq_comp_trans _ (nary link (nelist_concat_nelist As Ps)) _); [
              apply beh_eq_comp_sym; apply link_permutation; now apply nelist_concat_nelist_permutation
            | apply (beh_eq_comp_trans _ (nary link (nelist_concat_nelist As Qs)) _); [
                assumption | apply link_permutation; now apply nelist_concat_nelist_permutation
              ]
            ]).
    unfold As in HA2.
    rewrite (nelist_concat_nelist_nelist_concat_list Ps A0 As') in HA2.
    rewrite (nelist_concat_nelist_nelist_concat_list Qs A0 As') in HA2.
    rewrite (Hlink Ps (A0 :: As')) in HA2.
    now rewrite (Hlink Qs (A0 :: As')) in HA2.
  Qed.

  Lemma nz_md_ctx_eq_implies_fa_ctx_eq {L: md_language}:
    forall (n: nat) (Ps Qs: nelist component),
      md_ctx_eq (S n) Ps Qs ->
      fa_ctx_eq (nary link Ps) (nary link Qs).
  Proof.
    intros n Ps Qs H A.
    pose (nelist_cons _ A (replicate n empty)) as As.
    assert (length (nelist_to_list As) = S (length (replicate n empty)))
      as HAs by (unfold As; now unfold length).
    rewrite (replicate_length n empty) in HAs.
    pose (H (nelist_to_list As) HAs) as H0.
    assert (nelist_concat_list Ps (nelist_to_list As) =
            nelist_concat_list Ps ([A] ++ replicate n empty)) as H'Ps
        by (unfold As; now unfold nelist_to_list).
    rewrite H'Ps in H0.
    assert (nelist_concat_list Ps ([A] ++ replicate n empty) =
            nelist_concat_list (nelist_concat_list Ps [A])
                               (replicate n empty)) as H''Ps
        by (destruct Ps as [P Ps'];
            unfold nelist_concat_list;
            now rewrite (app_assoc)).
    rewrite H''Ps in H0.
    assert (nelist_concat_list Qs (nelist_to_list As) =
            nelist_concat_list Qs ([A] ++ replicate n empty)) as H'Qs
        by (unfold As; now unfold nelist_to_list).
    rewrite H'Qs in H0.
    assert (nelist_concat_list Qs ([A] ++ replicate n empty) =
            nelist_concat_list (nelist_concat_list Qs [A])
                               (replicate n empty)) as H''Qs
        by (destruct Qs as [Q Qs'];
            unfold nelist_concat_list;
            now rewrite (app_assoc)).
    rewrite H''Qs in H0.
    assert (beh_eq_comp
              (nary link (nelist_concat_list Ps [A]))
              (nary link (nelist_concat_list Qs [A]))
           ) as H1
        by (apply (beh_eq_comp_trans
                     _ (nary link (nelist_concat_list
                                     (nelist_concat_list Ps [A])
                                     (replicate n empty))) _); [
              apply beh_eq_comp_sym; now apply nary_link_empty
            | apply (beh_eq_comp_trans
                       _ (nary link (nelist_concat_list
                                       (nelist_concat_list Qs [A])
                                       (replicate n empty))) _); [
                assumption | now apply nary_link_empty
              ]
            ]).
    assert (nelist_concat_list Ps [A] = nelist_concat_nelist Ps (nelist_cons _ A []))
      as HPs''
        by now unfold nelist_concat_nelist.
    assert (nelist_concat_list Qs [A] = nelist_concat_nelist Qs (nelist_cons _ A []))
      as HQs''
        by now unfold nelist_concat_nelist.
    rewrite HPs'' in H1.
    rewrite HQs'' in H1.
    rewrite (nary_nelist_snoc link Ps A) in H1.
    rewrite (nary_nelist_snoc link Qs A) in H1.
    apply (beh_eq_comp_trans _ (link (nary link Ps) A) _); [
        apply beh_eq_comp_sym; now apply link_comm
      | apply (beh_eq_comp_trans _ (link (nary link Qs) A) _); [
          assumption | now apply link_comm
        ]
      ].
  Qed.

  Lemma z_md_ctx_eq_beh_eq_comp {L: md_language}:
    forall (Ps Qs: nelist component),
      md_ctx_eq 0 Ps Qs
      <->
      beh_eq_comp (nary link Ps) (nary link Qs).
  Proof.
    intros Ps Qs.
    assert (nelist_concat_list Ps [] = Ps) as HPs by apply nelist_concat_nil.
    assert (nelist_concat_list Qs [] = Qs) as HQs by apply nelist_concat_nil.
    split; intro H.
    + pose (H [] (eq_refl (length []))) as H'.
      rewrite HPs in H'.
      now rewrite HQs in H'.
    + intros As HAs.
      assert (As = []) as HnilAs
          by (destruct As; [reflexivity | compute in HAs; now exfalso]).
      rewrite HnilAs.
      rewrite HPs.
      now rewrite HQs.
  Qed.

  Lemma z_md:
    forall (Ps Qs: nelist (@component src)),
      md_ctx_eq 0 Ps Qs
      <->
      md_ctx_eq 0 (nelist_map compile Ps) (nelist_map compile Qs).
  Proof.
    intros Ps Qs.
    split.
    + intro H0.
      assert (beh_eq_comp (nary link Ps) (nary link Qs)) as H1
          by now apply z_md_ctx_eq_beh_eq_comp.
      assert (beh_eq_comp (compile (nary link Ps))
                          (compile (nary link Qs))) as H2
          by now apply correct_compilation.
      assert (beh_eq_comp (nary link (nelist_map compile Ps))
                          (nary link (nelist_map compile Qs))) as H3
          by (apply (beh_eq_comp_trans _ (compile (nary link Ps)) _); [
                apply beh_eq_comp_sym; apply fa_ctx_eq_implies_beh_eq; now apply separate_compilation
              | apply (beh_eq_comp_trans _ (compile (nary link Qs)) _); [
                  assumption | apply fa_ctx_eq_implies_beh_eq; now apply separate_compilation
                ]
              ]).
      now apply z_md_ctx_eq_beh_eq_comp.
    + intro H4.
      assert (beh_eq_comp (nary link (nelist_map compile Ps))
                          (nary link (nelist_map compile Qs))) as H3
          by now apply z_md_ctx_eq_beh_eq_comp.
      assert (beh_eq_comp (compile (nary link Ps))
                          (compile (nary link Qs))) as H2
          by (apply (beh_eq_comp_trans _ (nary link (nelist_map compile Ps)) _); [
                apply fa_ctx_eq_implies_beh_eq; now apply separate_compilation
              | apply (beh_eq_comp_trans _ (nary link (nelist_map compile Qs)) _); [
                  assumption | apply beh_eq_comp_sym; apply fa_ctx_eq_implies_beh_eq; now apply separate_compilation
                ]
              ]).
      assert (beh_eq_comp (nary link Ps) (nary link Qs)) as H1
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
    intros n n_att n_prog Hn Ps Qs HnPs HnQs.
    destruct (FA (nary link Ps) (nary link Qs)) as [FA' FA''].
    destruct n_att as [|n_att'].
    + exact (z_md Ps Qs).
    + pose (S n_att') as n_att.
      split.
      * intro H.
        assert (md_ctx_eq n_att Ps Qs) as Hmd_ctx_eq_src
            by exact H.
        assert (fa_ctx_eq (nary link Ps) (nary link Qs)) as Hfa_ctx_eq_src
            by now apply (nz_md_ctx_eq_implies_fa_ctx_eq n_att').
        assert (fa_ctx_eq (compile (nary link Ps)) (compile (nary link Qs)))
          as Hfa_ctx_eq_tgt
            by (unfold fa_ctx_eq; now apply FA').
        assert (fa_ctx_eq (nary link (nelist_map compile Ps))
                          (nary link (nelist_map compile Qs)))
          as Hfa_ctx_eq_tgt'
            by (apply (fa_ctx_eq_trans _ (compile (nary link Ps)) _); [
                  apply fa_ctx_eq_sym; now apply separate_compilation
                | apply (fa_ctx_eq_trans _ (compile (nary link Qs)) _); [
                    assumption
                  | now apply separate_compilation
                  ]
                ]).
        assert (md_ctx_eq n_att (nelist_map compile Ps)
                                (nelist_map compile Qs))
          as Hmd_ctx_eq_tgt
            by now apply (fa_ctx_eq_implies_nz_md_ctx_eq n_att').
        exact Hmd_ctx_eq_tgt.
      * intro H.
        assert (md_ctx_eq n_att (nelist_map compile Ps)
                                (nelist_map compile Qs))
          as Hmd_ctx_eq_tgt
            by exact H.
        assert (fa_ctx_eq (nary link (nelist_map compile Ps))
                          (nary link (nelist_map compile Qs)))
          as Hfa_ctx_eq_tgt
            by now apply (nz_md_ctx_eq_implies_fa_ctx_eq n_att').
        assert (fa_ctx_eq (compile (nary link Ps)) (compile (nary link Qs)))
          as Hfa_ctx_eq_tgt'
            by (apply (fa_ctx_eq_trans _ (nary link (nelist_map compile Ps)) _); [
                  now apply separate_compilation
                | apply (fa_ctx_eq_trans _ (nary link (nelist_map compile Qs)) _); [
                    assumption
                  | apply fa_ctx_eq_sym; now apply separate_compilation
                  ]
                ]).
        assert (fa_ctx_eq (nary link Ps) (nary link Qs)) as Hfa_ctx_eq_src
            by (unfold fa_ctx_eq; now apply FA'').
        assert (md_ctx_eq n_att Ps Qs) as Hmd_ctx_eq_src
            by now apply (fa_ctx_eq_implies_nz_md_ctx_eq n_att').
        exact Hmd_ctx_eq_src.
  Qed.

End FullAbstractionImpliesMutualDistrust.
