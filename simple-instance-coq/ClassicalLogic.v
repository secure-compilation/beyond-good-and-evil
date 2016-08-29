Axiom excluded_middle :
  forall P, P \/ ~P.

Theorem double_negation_elimination :
  forall P, ~~P -> P.
Proof.
  intros.
  pose (excluded_middle P) as EX.
  destruct EX.
  - apply H0.
  - apply H in H0. contradiction.
Qed.

Theorem double_negation_insertion :
  forall P:Prop, P -> ~~P.
Proof.
  intros. unfold not.
  intro contra. apply contra in H.
  contradiction.
Qed.

Theorem not_exists_dist :
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  pose excluded_middle as excl_mid.
  intros X P H.
  intros x.
  assert ( P x \/ ~ P x).
  apply excl_mid.
  inversion H0.
  apply H1.
  exfalso.
  unfold not in H.
  apply H.
  unfold not in H1.
  exists x.
  apply H1.
Qed.

Lemma de_morgan_not_or_not :
  forall P Q,
  ~(~P \/ ~Q) -> P /\ Q.
Proof.
  intros. split.
  - pose (excluded_middle P) as Ex_P.
    destruct Ex_P.
    + apply H0.
    + exfalso. apply H. left. apply H0.
  - pose (excluded_middle Q) as Ex_Q.
    destruct Ex_Q.
    + apply H0.
    + exfalso. apply H. right. apply H0.
Qed.

Lemma de_morgan_not_or_not' :
  forall P Q,
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros. unfold not in H.
  split.
  - intro contra.
    assert (P \/ Q). left; apply contra.
    apply H in H0; contradiction.
  - intro contra.
    assert (P \/ Q). right; apply contra.
    apply H in H0. contradiction.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intro E.
  inversion E as [ x Hx ].
  apply Hx.
  apply H.
Qed.

Theorem not_forall_dist : forall (X:Type) (P : X -> Prop),
  ~(forall x, P x) -> (exists x, ~ P x).
Proof.
  intros X P H.
  pose (excluded_middle (exists x, ~ P x)) as EX.
  destruct EX.
  - apply H0.
  - assert (forall x : X, P x) as Ha.
    { apply not_exists_dist. apply H0. }
    apply H in Ha. contradiction.
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
