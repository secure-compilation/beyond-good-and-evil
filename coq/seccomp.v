Require Import Coq.Arith.EqNat.

Section FinitePartialMaps.

  (* finite partial maps from nat to T *)
  Inductive fpm (T: Set): Set :=
  | fpm_empty: fpm T
  | fpm_cons: nat -> T -> fpm T -> fpm T.

  Inductive fpm_result {T: Set}: fpm T -> nat -> T + unit -> Prop :=
  | fpm_result_empty: forall (p: nat),
                        fpm_result (fpm_empty T) p (inr tt)
  | fpm_result_cons_eq: forall (p: nat) (t: T) (m: fpm T),
                          fpm_result (fpm_cons T p t m) p (inl t)
  | fpm_result_cons_neq: forall (res: T + unit) (n: nat) (p: nat)
                                (t: T) (m: fpm T),
                           n <> p ->
                           fpm_result m n res ->
                           fpm_result (fpm_cons T p t m) n res.

  Definition fpm_not_in_dom {T: Set} (m: fpm T) (n: nat) :=
    fpm_result m n (inr tt).

  Definition fpm_in_dom {T: Set} (m: fpm T) (n: nat) :=
    fpm_result m n (inr tt) -> False.
  
  Inductive fpm_disjoint {T: Set}: fpm T -> fpm T -> Prop :=
  | fpm_disjoint_empty: forall (m:fpm T),
                          fpm_disjoint m (fpm_empty T)
  | fpm_disjoint_cons: forall (m:fpm T) (p: nat) (t: T) (m': fpm T),
                         fpm_disjoint m m' ->
                         fpm_not_in_dom m p ->
                         fpm_disjoint m (fpm_cons T p t m')
  .

  Definition fpm_disjoint_union {T: Set} (m m': fpm T) (H: fpm_disjoint m m'): fpm T :=
    (fix f m0 :=
       match m0 with
         | fpm_empty => m'
         | fpm_cons p t m1 => fpm_cons T p t (f m1)
       end) m.

  Fixpoint fpm_as_function {T: Set} (m: fpm T) (n: nat): T + unit :=
    match m with
      | fpm_empty => inr tt
      | fpm_cons p t m' =>
        if beq_nat n p then inl t else fpm_as_function m' n
    end.

  Theorem fpm_translation_correct: forall {T: Set} (m: fpm T) (n: nat),
                                     fpm_result m n (fpm_as_function m n).
  Proof.
    induction m as [| p t m'].
    + intro n; compute; apply fpm_result_empty.
    + intro n.
      unfold fpm_as_function.
      assert (beq_nat n p = true \/ beq_nat n p = false) as H
          by (destruct (beq_nat n p); [left | right]; reflexivity).
      destruct H.
      * pose (beq_nat_true n p H) as Heq.
        rewrite H.
        inversion Heq.
        apply (fpm_result_cons_eq p t m').
      * pose (beq_nat_false n p H) as Hneq.
        rewrite H.
        apply (fpm_result_cons_neq (fpm_as_function m' n)
                                   n p t m').
        assumption.
        apply (IHm' n).
  Qed.

  Theorem fpm_translation_complete: forall {T: Set} (m: fpm T) (n: nat) (res: T + unit),
                                      fpm_result m n res -> res = (fpm_as_function m n).
  Proof.
    intros T m n res H; induction H; unfold fpm_as_function; [
      reflexivity
    | now rewrite <- (beq_nat_refl p)
    | destruct (beq_nat_false_iff n p) as [_ Hneqfalse]; now rewrite (Hneqfalse H)
    ].
  Qed.

  Theorem fpm_result_deterministic:
    forall {T: Set} (m: fpm T) (n: nat) (res: T + unit),
      fpm_result m n res ->
      forall res', fpm_result m n res' -> res = res'.
  Proof.
    intros T m n res H res' H'.
    pose (fpm_translation_complete m n res H) as Hres.
    pose (fpm_translation_complete m n res' H') as Hres'.
    rewrite Hres.
    rewrite Hres'.
    reflexivity.
  Qed.

  Theorem fpm_in_dom_or_not_in_dom:
    forall {T: Set} (m: fpm T) (n: nat),
    fpm_in_dom m n \/ fpm_not_in_dom m n.
  Proof.
    intros T m n.
    unfold fpm_in_dom.
    unfold fpm_not_in_dom.
    remember (fpm_as_function m n) as res.
    pose (fpm_translation_correct m n) as H.
    destruct res.
    + left.
      intro H'.
      rewrite <- Heqres in H.
      pose (fpm_result_deterministic m n (inl t) H (inr tt) H') as Habs.
      inversion Habs.
    + right.
      destruct u.
      now rewrite <- Heqres in H.
  Qed.

  Theorem fpm_disjoint_union_characterization:
    forall {T: Set} (m m': fpm T) (H: fpm_disjoint m m'),
      let m'' := fpm_disjoint_union m m' H in
      forall n (t: T),
        (fpm_result m n (inl t) -> fpm_result m'' n (inl t))
        /\
        (fpm_result m' n (inl t) -> fpm_result m'' n (inl t))
        /\
        (fpm_result m'' n (inl t) -> fpm_result m n (inl t) \/ fpm_result m' n (inl t)).
  Proof.
    admit.
  Qed.
    
End FinitePartialMaps.

Section Definitions.

  Parameter (language: Set).
  Parameter (src tgt: language).
  Parameter (component: language -> Set).
  Definition prog (L: language): Set := fpm (component L).
  Parameter compile: prog src -> prog tgt.
  
  Parameter (compatible: forall {L: language}, prog L -> prog L -> Prop).
  Parameter (complete: forall {L: language}, prog L -> Prop).

  Parameter (merge: forall {L: language} (P Q: prog L),
                      compatible P Q -> prog L).
  Parameter (obs_eq: forall (L: language) (P Q: prog L),
                     complete P -> complete Q -> Prop).

  Definition same_compatibility {L: language} (P Q: prog L) :=
    forall (A: prog L), (compatible P A <-> compatible Q A).
  
  Definition same_complete_compatibility {L: language} (P Q: prog L) :=
    same_compatibility P Q
    /\
    (forall (A: prog L)
            (HPA: compatible P A) (HQA: compatible Q A),
       complete (merge P A HPA) <-> complete (merge Q A HQA)).

  Theorem same_complete_compatibility_compatible_implication:
    forall {L: language} (P Q A: prog L),
      same_complete_compatibility P Q ->
      compatible P A ->
      compatible Q A.

  Theorem same_complete_compatibility_complete_implication:
    forall {L: language} (P Q A: prog L),
      same_complete_compatibility P Q ->
      compatible P A ->
      complete (merge P A) ->
  complete .
    
  Definition ctx_eq (L: language) (P Q: prog L) (H: same_compatibility P Q) :=
    forall (A: prog language)
           (Hcompat: compatible P A)
           (Hcomplete: complete (merge P A Hcompat)),
      let Hcompat' := same_complete_compatibility_compatible_implication P Q A H Hcompat in
      let Hcomplete' := same_complete_compatibility_compatible_implication P Q A H Hcompat in
  .
  
  Hypothesis compatible_implies_disjoint:
    forall (L: language) (P Q: prog L),
      compatible P Q -> fpm_disjoint P Q.
  Hypothesis merge_is_disjoint_union:
    forall (L: language) (P Q: prog L) (H: compatible P Q),
      let H' := compatible_implies_disjoint L P Q H in
      merge P Q H = fpm_disjoint_union P Q H'.

  Definition full_abstraction: Prop :=
    forall (P Q: prog src), ctx_eq src P Q <-> ctx_eq tgt (compile P) (compile Q).
  
End Definitions.