Require Import Coq.Lists.List.
Import ListNotations.

Require Import MutualDistrust.fullabst.
Require Import MutualDistrust.lib.

Arguments Some {A} _.
Arguments fst {_ _} _.
Arguments snd {_ _} _.

Class interface_language (interface: Type): Type :=
  {
    compatible: list interface -> Prop;
    complete: list interface -> Prop
  }.

Let comp
    {interface: Type}
    `{interface_language interface}
    (Is : list interface) := compatible Is /\ complete Is.

Class component_language
      {interface: Type} (il: interface_language interface)
      (component program: Type): Type :=
  {
    get_interface : component -> option interface;
    link : list component -> program;
    fully_defined : list component -> list interface -> Prop;
    beh_eq : program -> program -> Prop
  }.

Definition has_interface
           {interface: Type} {il: interface_language interface}
           {component program: Type}
           {L: component_language il component program}

           (C: component) (I: interface): Prop :=
  get_interface C = Some I.

Notation "P ~~ Q" := (beh_eq P Q) (at level 60, no associativity).

Fixpoint All {A} (P : A -> Prop) (l : list A) : Prop :=
  match l with
  | [] => True
  | a :: l' => P a /\ All P l'
  end.

Lemma All_app {A} (P : A -> Prop) (l1 l2 : list A) :
  All P l1 ->
  All P l2 ->
  All P (l1 ++ l2).
Proof.
  induction l1 as [|x l1 IH]; simpl; try solve [intuition].
Qed.

Lemma All_app_l {A} (P : A -> Prop) (l1 l2 : list A) :
  All P (l1 ++ l2) ->
  All P l1.
Proof.
  induction l1 as [|x l1 IH]; simpl; try solve [intuition].
Qed.

Lemma All_app_r {A} (P : A -> Prop) (l1 l2 : list A) :
  All P (l1 ++ l2) ->
  All P l2.
Proof.
  induction l1 as [|x l1 IH]; simpl; try solve [intuition].
Qed.

Fixpoint All2 {A B} (P : A -> B -> Prop) l1 l2 : Prop :=
  match l1, l2 with
  | [], [] => True
  | a :: l1', b :: l2' => P a b /\ All2 P l1' l2'
  | _, _ => False
  end.

Lemma All2_All {A B} (P : A -> B -> Prop) l1 l2 :
  All2 P l1 l2 ->
  All (fun p => P (fst p) (snd p)) (combine l1 l2).
Proof.
  revert l2.
  induction l1 as [|x l1 IH]; intros [|y l2]; simpl; try solve [intuition].
Qed.

Lemma All_All2 {A B} (P : A -> B -> Prop) l1 l2 :
  length l1 = length l2 ->
  All (fun p => P (fst p) (snd p)) (combine l1 l2) ->
  All2 P l1 l2.
Proof.
  revert l2.
  induction l1 as [|x l1 IH]; intros [|y l2]; simpl;
  try solve [intuition|discriminate].
Qed.

Lemma All2_length {A B} (P : A -> B -> Prop) l1 l2 :
  All2 P l1 l2 ->
  length l1 = length l2.
Proof.
  revert l2; induction l1 as [|x1 l1 IH]; intros [|x2 l2]; simpl; intuition.
Qed.

Definition mutual_distrust
  {interface: Type} {I : interface_language interface}
  {hcomponent hprogram: Type} {lcomponent lprogram: Type}

  (H: component_language I hcomponent hprogram)
  (L: component_language I lcomponent lprogram)
  (compile : hcomponent -> lcomponent) :=

  forall PIs AIs : list interface,
  comp (PIs ++ AIs) ->
  forall Ps : list hcomponent, All2 has_interface Ps PIs ->
  forall Qs : list hcomponent, All2 has_interface Qs PIs ->
  ((forall As : list hcomponent, All2 has_interface As AIs ->
     link (Ps ++ As) ~~ link (Qs ++ As))
   <->
   (forall az : list lcomponent, All2 has_interface az AIs ->
         link (map compile Ps ++ az)
      ~~ link (map compile Qs ++ az))).

(* Instantiating structured full abstraction to obtain something
   stronger than mutual distrust (we will use this to prove mutual
   distrust for our compiler) *)

Coercion is_true : bool >-> Sortclass. (* Prop *)

Definition fst_map {A B C} (f : A -> C) (p : A * B) :=
  (f (fst p), snd p).

Fixpoint somes {A} (l : list (option A)) : list A :=
  match l with
  | [] => []
  | Some a :: l' => a :: somes l'
  | None :: l' => somes l'
  end.

Lemma somes_app {A} (l1 l2 : list (option A)) :
  somes (l1 ++ l2) = somes l1 ++ somes l2.
Proof.
  induction l1 as [|[x|] l1 IH]; simpl; trivial.
  now rewrite IH.
Qed.

Lemma somes_map {A} (l : list A) :
  somes (map Some l) = l.
Proof.
  now induction l as [|x l IH]; simpl; trivial; rewrite IH.
Qed.

Definition isSome {A} (oa : option A) :=
  match oa with
  | Some _ => true
  | _ => false
  end.

Definition fsts {A B} (l : list (A * B)) : list A :=
  map fst l.

Definition snds {A B} (l : list (A * B)) : list B :=
  map snd l.

Lemma fsts_combine {A B} (l1 : list A) (l2 : list B) :
  length l1 = length l2 ->
  map fst (combine l1 l2) = l1.
Proof.
  revert l2.
  induction l1 as [|x l1 IH]; simpl; intros [|y l2];
  simpl; trivial; try discriminate.
  intros H. rewrite IH; congruence.
Qed.

Lemma snds_combine {A B} (l1 : list A) (l2 : list B) :
  length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  revert l2.
  induction l1 as [|x l1 IH]; simpl; intros [|y l2];
  simpl; trivial; try discriminate.
  intros H. rewrite IH; congruence.
Qed.

Section SFAfromMD.

Context {interface: Type} {I: interface_language interface} {component program: Type}.
Context (compl : component_language I component program).

(* We take both SFA programs and contexts to be "partial programs"
   of the following type *)
Definition pprog := list (option (component*interface)).

Fixpoint merge (p:pprog) (q:pprog) : option pprog :=
  match p, q with
  | [], [] => Some []
  | Some (c,i1) :: p', None :: q'
  | None :: p', Some (c,i1) :: q' =>
    match merge p' q' with
    | Some pq' => Some (Some (c,i1) :: pq')
    | None     => None
    end
  | None :: p', None :: q' =>
    match merge p' q' with
    | Some pq' => Some (None :: pq')
    | None     => None
    end
  | _, _ => None
  end.

Lemma merge_app p1 p2 q1 q2 :
  length p1 = length q1 ->
  merge (p1 ++ p2) (q1 ++ q2) =
  match merge p1 q1, merge p2 q2 with
  | Some m1, Some m2 => Some (m1 ++ m2)
  | _, _ => None
  end.
Proof.
  revert q1.
  induction p1 as [|[[cp ip]|] p1 IH]; intros [|[[cq iq]|] q1];
  simpl; trivial; try discriminate.
  - now destruct (merge p2 q2).
  - intros H. inversion H as [H'].
    rewrite (IH _ H').
    destruct (merge p1 q1) as [m1|]; trivial.
    destruct (merge p2 q2) as [m2|]; trivial.
  - intros H. inversion H as [H'].
    rewrite (IH _ H').
    destruct (merge p1 q1) as [m1|]; trivial.
    destruct (merge p2 q2) as [m2|]; trivial.
  - intros H. inversion H as [H'].
    rewrite (IH _ H').
    destruct (merge p1 q1) as [m1|]; trivial.
    destruct (merge p2 q2) as [m2|]; trivial.
Qed.

Lemma merge_None_Some n Ps :
  n = length Ps ->
  merge (repeat None n) (map Some Ps) = Some (map Some Ps).
Proof.
  intros ->.
  induction Ps as [|[CP IP] Ps IH]; simpl; trivial.
  now rewrite IH.
Qed.

Lemma merge_Some_None n Ps :
  n = length Ps ->
  merge (map Some Ps) (repeat None n) = Some (map Some Ps).
Proof.
  intros ->.
  induction Ps as [|[CP IP] Ps IH]; simpl; trivial.
  now rewrite IH.
Qed.

Definition interfaces_ok (p:pprog) :=
  All (fun PIP => has_interface (fst PIP) (snd PIP)) (somes p).

Definition stat_eq (p q : pprog) :=
    All2 (fun optPIP optQIQ =>
            match optPIP, optQIQ with
            | None, None => True
            | Some (P, IP), Some (Q, IQ) =>
              has_interface P IP /\ has_interface Q IQ /\ IP = IQ
            | _, _ => False
            end) p q.

Lemma merge_stat_eq As Ps Qs CP :
  merge As Ps = Some CP ->
  stat_eq Ps Qs ->
  match merge As Qs with
  | Some CQ => snds (somes CP) = snds (somes CQ)
  | None => False
  end.
Proof.
revert Ps Qs CP. induction As as [|[[A IA]|] As IH].
- unfold stat_eq.
  intros [] []; simpl; try congruence.
  intros CP H. now inversion H.
- unfold stat_eq in *.
  intros [|[[P IP]|] Ps] [|[[Q IQ]|] Qs]; simpl; try solve [congruence|intuition].
  intros CP.
  destruct (merge As Ps) as [CP'|] eqn:mergeAsPs; try discriminate.
  intros H. inversion H; subst CP; clear H.
  intros [_ HPsQs].
  specialize (IH _ _ _ mergeAsPs HPsQs).
  destruct (merge As Qs) as [CQ'|] eqn:mergeAsQs; try solve [intuition].
  now simpl; rewrite IH.
- unfold stat_eq in *.
  intros [|[[P IP]|] Ps] [|[[Q IQ]|] Qs]; simpl; try solve [congruence|intuition].
  + intros CP.
    destruct (merge As Ps) as [CP'|] eqn:mergeAsPs; try discriminate.
    intros H. inversion H; subst CP; clear H.
    intros [[PI [QI H]] HPsQs]. subst IQ. rename IP into IPQ.
    specialize (IH _ _ _ mergeAsPs HPsQs).
    destruct (merge As Qs) as [CQ'|] eqn:mergeAsQs; try solve [intuition].
    now simpl; rewrite IH.
  + intros CP.
    destruct (merge As Ps) as [CP'|] eqn:mergeAsPs; try discriminate.
    intros H. inversion H; subst CP; clear H.
    intros [_ HPsQs].
    specialize (IH _ _ _ mergeAsPs HPsQs).
    destruct (merge As Qs) as [CQ'|] eqn:mergeAsQs; solve [intuition].
Qed.

Definition shape := list (bool*interface). (* replace (bool*interface) with option interface
                                              if dropping scl_program_has_shape *)
Definition flip_shape (s : shape): shape :=
  List.map (fun bi => match bi with (b, i) => (negb b, i) end) s.

Fixpoint context_has_shape (s : shape) (c : pprog) : Prop :=
  match s, c with
  | [], [] => true
  | (true,i1)::s', (Some (p,i2))::c' =>
    has_interface p i2 /\ i1 = i2 /\ context_has_shape s' c'
  | (false,_)::s', None::c' =>
    context_has_shape s' c'
  | _, _ => false
  end.

Lemma context_has_shape_app_l s1 s2 p :
  context_has_shape (s1 ++ s2) p ->
  exists p1 p2,
    p = p1 ++ p2
    /\ context_has_shape s1 p1
    /\ context_has_shape s2 p2.
Proof.
  revert p.
  induction s1 as [|[b i] s1 IH]; intros p.
  - exists [], p; simpl.
    repeat split; trivial.
  - destruct b, p as [|[[cp ip]|] p]; simpl; try discriminate.
    + intros [H1 [H2 H3]].
      specialize (IH _ H3).
      destruct IH as [p1 [p2 [Hp1 [Hp2 Hp3]]]].
      rewrite Hp1.
      exists (Some (cp, ip) :: p1), p2; repeat split; trivial.
    + intros H. specialize (IH _ H).
      destruct IH as [p1 [p2 [Hp1 [Hp2 Hp3]]]]. rewrite Hp1.
      exists (None :: p1), p2; repeat split; trivial.
Qed.

Lemma context_has_shape_app s1 s2 p1 p2 :
  context_has_shape s1 p1 ->
  context_has_shape s2 p2 ->
  context_has_shape (s1 ++ s2) (p1 ++ p2).
Proof.
  intros H1 H2. revert p1 H1.
  induction s1 as [|[[] i] s1 IH]; intros [|[[cp ip]|] ps]; simpl;
  try discriminate; trivial.
  - intros [H11 [H12 H13]].
    subst ip. repeat split; trivial.
    now eauto.
  - now eauto.
Qed.

Lemma context_has_shape_length s p :
  context_has_shape s p ->
  length s = length p.
Proof.
  revert p. induction s as [|[b i] s IH]; intros p; simpl.
  - destruct p; simpl; trivial; discriminate.
  - destruct b, p as [|[[cp ip]|] p]; simpl; try discriminate.
    + intros [_ [_ H]]. rewrite (IH _ H). reflexivity.
    + intros H. rewrite (IH _ H). reflexivity.
Qed.

Lemma context_has_shape_false PIs AA :
  context_has_shape (map (pair false) PIs) AA ->
  AA = repeat None (length PIs).
Proof.
  revert AA; induction PIs as [|Is PIs IH]; intros [|A AA]; simpl; trivial; try discriminate.
  destruct A; trivial; try discriminate.
  intros H. rewrite (IH _ H). reflexivity.
Qed.

Lemma context_has_shape_false_conv PIs n :
  n = length PIs ->
  context_has_shape (map (pair false) PIs) (repeat None n).
Proof.
  intros ->.
  induction PIs as [|PI PIs IH]; simpl; trivial; reflexivity.
Qed.

Lemma context_has_shape_true PIs AA :
  context_has_shape (map (pair true) PIs) AA ->
  exists AA',
    AA = map Some (combine AA' PIs)
    /\ All2 has_interface AA' PIs.
Proof.
  revert AA.
  induction PIs as [|PI PIs IH]; intros AA; simpl.
  - destruct AA; try discriminate.
    intros _. exists [].
    now split; simpl; trivial.
  - destruct AA as [|[[CA IA]|] AA]; try discriminate.
    intros [H1 [H2 H3]]. simpl.
    destruct (IH _ H3) as [AA' [? H4]].
    subst AA. exists (CA :: AA'). simpl. repeat split; congruence.
Qed.

Lemma context_has_shape_true_conv PIs AA :
  All2 has_interface AA PIs ->
  context_has_shape (map (pair true) PIs) (map Some (combine AA PIs)).
Proof.
  revert AA.
  induction PIs as [|PI PIs IH]; intros [|A AA]; simpl;
  try solve [intuition discriminate|reflexivity].
  intros [H1 H2]. repeat split; auto.
Qed.

Definition context_fully_defined (p : pprog) (s : shape) : Prop :=
  fully_defined (fsts (somes p))
                (somes (map (fun i : bool * _ => if fst i then None else Some (snd i)) s)).

Definition program_has_shape (s : shape) (p : pprog) : Prop :=
  context_has_shape (flip_shape s) p.

Definition program_fully_defined (p : pprog) (s : shape) : Prop :=
  context_fully_defined p (flip_shape s).

Lemma stat_eq_shape Ps Qs s :
  stat_eq Ps Qs ->
  program_has_shape s Ps ->
  program_has_shape s Qs.
Proof.
revert Qs s. unfold stat_eq.
induction Ps as [|[[P IP]|] Ps IH];
intros [|[[Q IQ]|] Qs] [|[b Is] s]; simpl; try solve [intuition].
- intros [[HPI [HQI HI]]]. subst IQ. rename IP into IPQ.
  unfold program_has_shape; simpl.
  destruct b; simpl; trivial.
  intros H [_ [HIs HPs]]. subst Is.
  repeat split; trivial.
  exact (IH _ _ H HPs).
- unfold program_has_shape; simpl.
  destruct b; simpl; trivial.
  intros [_ H] HPs.
  exact (IH _ _ H HPs).
Qed.

Definition insert c p :=
  match merge c p with
  | Some cp => cp
  | None => [] (* shouldn't happen *)
  end.

(* FIXME: It is a bit strange that [cl_compatible] is a property of [c]
   and [p] separately when in this instance we factor it through
   [merge c p]. This makes it very similar to how we use [cl_complete]
   in e.g. [cl_stat_eq_compatible_complete].  *)

Definition comp_compatible c p :=
  match merge c p with
  | Some cp => interfaces_ok cp /\ compatible (snds (somes cp))
  | None => False
  end.

Definition comp_complete (p : pprog) :=
  All isSome p /\ complete (snds (somes p)).

Lemma merge_shape As Ps :
  (match merge As Ps with
   | Some CP => interfaces_ok CP /\ All isSome CP
   | None => False
   end)
  <-> exists s : shape,
        context_has_shape s As /\
        program_has_shape s Ps.
Proof.
revert Ps. unfold interfaces_ok, program_has_shape.
induction As as [|[[A IA]|] As IH].
- intros [|[[P IP]|] Ps]; simpl; split; try solve [intuition].
  + intros _. exists []. simpl.
    now repeat split; trivial.
  + intros [s [HAs HPs]].
    destruct s as [|[[] ?] s]; simpl in *;
    solve [inversion HPs|inversion HAs].
  + intros [s [HAs HPs]].
    destruct s as [|[[] ?] s]; simpl in *;
    solve [inversion HPs|inversion HAs].
- intros [|[[P IP]|] Ps]; simpl; split; try solve [intuition].
  + intros [s [HAs HPs]].
    destruct s as [|[[] ?] s]; simpl in *;
    solve [inversion HPs|inversion HAs].
  + intros [s [HAs HPs]].
    destruct s as [|[[] ?] s]; simpl in *;
    solve [inversion HPs|inversion HAs].
  + specialize (IH Ps).
    destruct (merge As Ps) as [CP|] eqn:mergeAsPs; try solve [intuition].
    simpl.
    rewrite and_assoc, (and_comm true), <- (and_assoc _ _ true), IH.
    intros [HIA [[s [HAs HPs]] _]]. exists ((true, IA) :: s). simpl.
    repeat split; trivial.
  + specialize (IH Ps).
    intros [s [HAs HPs]].
    destruct s as [|[[] i] s]; simpl in *;
    try solve [inversion HPs|inversion HAs].
    destruct HAs as [HIA [? HAs]]. subst i.
    assert (H : exists s', context_has_shape s' As /\ context_has_shape (flip_shape s') Ps) by eauto.
    rewrite <- IH in H.
    destruct (merge As Ps) as [CP|] eqn:mergeAsPs; try solve [intuition].
    simpl. intuition (split; eauto).
- intros [|[[P IP]|] Ps]; simpl; split; try solve [intuition].
  + intros [s [HAs HPs]].
    destruct s as [|[[] ?] s]; simpl in *;
    solve [inversion HPs|inversion HAs].
  + specialize (IH Ps).
    destruct (merge As Ps) as [CP|] eqn:mergeAsPs; try solve [intuition].
    simpl.
    rewrite and_assoc, (and_comm true), <- (and_assoc _ _ true), IH.
    intros [HIA [[s [HAs HPs]] _]]. exists ((false, IP) :: s). simpl.
    repeat split; trivial.
  + specialize (IH Ps).
    intros [s [HAs HPs]].
    destruct s as [|[[] i] s]; simpl in *;
    try solve [inversion HPs|inversion HAs].
    destruct HPs as [HIP [? HPs]]. subst i.
    assert (H : exists s', context_has_shape s' As /\ context_has_shape (flip_shape s') Ps) by eauto.
    rewrite <- IH in H.
    destruct (merge As Ps) as [CP|] eqn:mergeAsPs; try solve [intuition].
    simpl. intuition (split; eauto).
  + specialize (IH Ps).
    destruct (merge As Ps) as [CP|] eqn:mergeAsPs; try solve [intuition].
    simpl. intros [_ [contra _]]. inversion contra.
  + intros [s [HAs HPs]].
    destruct s as [|[[] ?] s]; simpl in *;
    solve [inversion HPs|inversion HAs].
Qed.

Lemma stat_eq_compatible_complete Ps Qs :
  stat_eq Ps Qs ->
  forall A,
    comp_compatible A Ps /\ comp_complete (insert A Ps) ->
    comp_compatible A Qs /\ comp_complete (insert A Qs).
Proof.
  intros HPsQs As.
  unfold comp_compatible, comp_complete, insert in *.
  destruct (merge As Ps) as [CP|] eqn:mergeAsPs; try solve [intuition].
  intros [[int_CP comp_CP] [somes_AsPs compl_CP]].
  assert (H := merge_shape As Ps).
  rewrite mergeAsPs in H.
  assert (H' := conj int_CP somes_AsPs).
  rewrite H in H'. destruct H' as [s [HAs HPs]].
  assert (H' := stat_eq_shape Ps Qs s HPsQs HPs).
  assert (H'' : exists s, context_has_shape s As /\ program_has_shape s Qs) by eauto.
  rewrite <- merge_shape in H''.
  destruct (merge As Qs) as [CQ|] eqn:mergeAsQs; try solve [intuition].
  assert (H''' := merge_stat_eq _ _ _ _ mergeAsPs HPsQs).
  rewrite mergeAsQs in H'''.
  intuition congruence.
Qed.

Instance context_lang_from_component_lang :
     context_language pprog pprog :=
{
  cl_insert := insert;
  cl_compatible := comp_compatible;
  cl_complete := comp_complete;
  cl_stat_eq := stat_eq;
  cl_beh_eq p q := beh_eq (link (fsts (somes p))) (link (fsts (somes q)));
  cl_stat_eq_compatible_complete := @stat_eq_compatible_complete

}.

Instance structured_context_lang_from_component_lang :
     structured_context_language
       context_lang_from_component_lang
       shape :=
{
  scl_context_has_shape := context_has_shape;
  scl_context_fully_defined := context_fully_defined;
  scl_program_has_shape := program_has_shape;
  scl_program_fully_defined := program_fully_defined
}.

End SFAfromMD.

Section SFAimpliesMD.

Context {interface: Type} {I : interface_language interface}
        {hcomponent hprogram: Type} {lcomponent lprogram: Type}
        (H: component_language I hcomponent hprogram)
        (L: component_language I lcomponent lprogram)
        (compile : hcomponent -> lcomponent).

Hypothesis has_interface_compile :
  forall P PI, has_interface P PI ->
               has_interface (compile P) PI.

Definition map_compile (p:@pprog interface hcomponent) :
                          @pprog interface lcomponent :=
  List.map (option_map (fst_map compile)) p.

Theorem sfa_implies_md :
  structured_full_abstraction
    (structured_context_lang_from_component_lang H)
    (structured_context_lang_from_component_lang L)
    map_compile ->
  mutual_distrust H L compile.
Proof.
intros Hsfa PIs AIs Hcomp Ps HPs Qs HQs.
assert (HPQ : @stat_eq _ _ _ _
                       H
                       (map Some (combine Ps PIs) ++ repeat None (length AIs))
                       (map Some (combine Qs PIs) ++ repeat None (length AIs))).
{ clear Hcomp Hsfa. revert Ps HPs Qs HQs. unfold stat_eq.
  induction PIs as [|PI PIs IH]; intros [|P Ps] HPs [|Q Qs] HQs; simpl in *; try solve [intuition].
  generalize (length AIs). clear AIs HPs HQs.
  now induction 0 as [|n IH]; split. }
assert (HPs' : @program_has_shape _ _ _ _
                                  H
                                  (map (pair false) PIs ++ map (pair true) AIs)
                                  (map Some (combine Ps PIs) ++ repeat None (length AIs))).
{ clear Qs HQs HPQ Hcomp.
  revert PIs HPs. unfold program_has_shape.
  induction Ps as [|P Ps IH]; simpl; intros PIs HPs.
  - destruct PIs as [|]; simpl in *; try solve [intuition].
    clear HPs.
    induction AIs as [|AI AIs IH]; simpl; trivial.
    reflexivity.
  - destruct PIs as [|PI PIs]; simpl in *; try solve [intuition]. }
assert (HQs' : @program_has_shape _ _ _ _
                                  H
                                  (map (pair false) PIs ++ map (pair true) AIs)
                                  (map Some (combine Qs PIs) ++ repeat None (length AIs))).
{ clear Ps HPs HPs' HPQ Hcomp.
  revert PIs HQs. unfold program_has_shape.
  induction Qs as [|Q Qs IH]; simpl; intros PIs HQs.
  - destruct PIs as [|]; simpl in *; try solve [intuition].
    clear HQs.
    induction AIs as [|AI AIs IH]; simpl; trivial.
    reflexivity.
  - destruct PIs as [|PI PIs]; simpl in *; try solve [intuition]. }
specialize (Hsfa (map (pair false) PIs ++ map (pair true) AIs)
                 (map Some (combine Ps PIs) ++ repeat None (length AIs))
                 (map Some (combine Qs PIs) ++ repeat None (length AIs))).
specialize (Hsfa HPQ HPs' HQs'). simpl in Hsfa.
simpl in *. split.
- (* -> *)
  intros Heq az Haz. destruct Hsfa as [Hsfa _].
  assert (H' : (forall AA : pprog,
                 context_has_shape H (map (pair false) PIs ++ map (pair true) AIs)
                                   AA /\
                 comp_compatible H AA
                                 (map Some (combine Ps PIs) ++ repeat None (length AIs)) /\
                 comp_complete
                   (insert AA
                           (map Some (combine Ps PIs) ++ repeat None (length AIs))) ->
                 link
                   (fsts
                      (somes
                         (insert AA
                                 (map Some (combine Ps PIs) ++ repeat None (length AIs))))) ~~
                   link
                   (fsts
                      (somes
                         (insert AA
                                 (map Some (combine Qs PIs) ++ repeat None (length AIs))))))).
  { intros AA [Hshape [HcompAA Hcompl]].
    apply context_has_shape_app_l in Hshape.
    destruct Hshape as [AA1 [AA2 [E1 [E2 E3]]]].
    subst AA. unfold insert in *.
    assert (Hp : length AA1 = length (map Some (combine Ps PIs))).
    { rewrite map_length, combine_length, min_l.
      - rewrite <- (context_has_shape_length _ _ _ E2).
        rewrite map_length.
        now rewrite (All2_length _ _ _ HPs).
      - now rewrite (All2_length _ _ _ HPs). }
    rewrite (merge_app AA1 AA2 _ _ Hp) in *.
    assert (Hq : length AA1 = length (map Some (combine Qs PIs))).
    { rewrite map_length, combine_length, min_l.
      - rewrite <- (context_has_shape_length _ _ _ E2).
        rewrite map_length.
        now rewrite (All2_length _ _ _ HQs).
      - now rewrite (All2_length _ _ _ HQs). }
    rewrite (merge_app AA1 AA2 _ _ Hq) in *.
    pose proof (context_has_shape_false _ _ _ E2). subst AA1.
    rewrite merge_None_Some; try rewrite combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HPs); trivial.
    rewrite merge_None_Some; try rewrite combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HQs); trivial.
    apply context_has_shape_true in E3.
    destruct E3 as [AA2' [? HAA2']]. subst AA2.
    rewrite merge_Some_None; try rewrite combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HAA2'); trivial.
    rewrite !somes_app, !somes_map.
    unfold fsts. rewrite !map_app.
    rewrite !fsts_combine; trivial; eauto.
    - apply (All2_length _ _ _ HQs).
    - apply (All2_length _ _ _ HAA2').
    - apply (All2_length _ _ _ HPs). }
  specialize (Hsfa H'). clear H'.
  specialize (Hsfa (repeat None (length PIs) ++ map Some (combine az AIs))).
  unfold map_compile, insert, program_has_shape, flip_shape in *.
  rewrite !map_app, !map_map in *. simpl in *.
  rewrite map_repeat in Hsfa. simpl in *.
  repeat rewrite <- (map_map (fst_map compile) Some) in Hsfa.
  rewrite merge_app in Hsfa;
  try rewrite repeat_length, !map_length, combine_length, min_r; trivial;
  try rewrite (All2_length _ _ _ HPs); trivial.
  rewrite merge_None_Some in Hsfa;
  try rewrite map_length, combine_length, min_r; trivial;
  try rewrite (All2_length _ _ _ HPs); trivial.
  rewrite merge_Some_None in Hsfa;
  try rewrite combine_length, min_r; trivial; try rewrite (All2_length _ _ _ Haz); trivial.
  rewrite somes_app, !somes_map in Hsfa.
  rewrite merge_app in Hsfa;
  try rewrite repeat_length, !map_length, combine_length, min_r; trivial;
  try rewrite (All2_length _ _ _ HQs); trivial.
  rewrite merge_None_Some in Hsfa;
  try rewrite map_length, combine_length, min_r; trivial;
  try rewrite (All2_length _ _ _ HQs); trivial.
  rewrite merge_Some_None in Hsfa;
  try rewrite map_length; try rewrite combine_length, min_r; trivial;
  try rewrite (All2_length _ _ _ Haz); trivial.
  unfold fsts in Hsfa.
  rewrite map_app, fsts_combine in Hsfa; try rewrite (All2_length _ _ _ Haz); trivial.
  rewrite somes_app, !somes_map, map_app, !(map_map _ fst) in Hsfa.
  rewrite fsts_combine in Hsfa; try rewrite (All2_length _ _ _ Haz); trivial.
  rewrite (map_ext (fun x => fst (fst_map compile x)) (fun x => compile (fst x))) in Hsfa;
  try now intros [].
  rewrite (map_ext (fun x => fst (fst_map compile x)) (fun x => compile (fst x))) in Hsfa;
  try now intros [].
  rewrite <- !(map_map fst), !fsts_combine in Hsfa;
  try rewrite (All2_length _ _ _ HPs); trivial;
  try rewrite (All2_length _ _ _ HQs); trivial.
  apply Hsfa. clear Hsfa. repeat split.
  + apply context_has_shape_app.
    * now apply context_has_shape_false_conv.
    * now apply context_has_shape_true_conv.
  + unfold comp_compatible.
    rewrite merge_app; try rewrite repeat_length, !map_length, combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HPs); trivial.
    rewrite merge_None_Some; try rewrite map_length, combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HPs); trivial.
    rewrite merge_Some_None; try rewrite combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ Haz); trivial.
    split.
    * unfold interfaces_ok.
      rewrite somes_app, !somes_map.
      apply All_app; try now apply All2_All.
      clear - Ps PIs HPs has_interface_compile.
      revert PIs HPs.
      now induction Ps as [|P Ps IH]; intros [|PI PIs]; simpl; intuition.
    * unfold snds.
      rewrite somes_app, !somes_map, map_app, snds_combine;
      try rewrite (All2_length _ _ _ Haz); trivial.
      rewrite map_map.
      rewrite (map_ext (fun x => snd (fst_map compile x)) snd); try now intros [].
      rewrite snds_combine; try rewrite (All2_length _ _ _ HPs); trivial.
      exact (proj1 Hcomp).
  + rewrite <- map_app.
    generalize (map (fst_map compile) (combine Ps PIs) ++ combine az AIs).
    clear.
    now intros PIs; induction PIs as [|PI PIs IH]; simpl; intuition.
  + unfold snds.
    rewrite somes_app, !somes_map, map_app, snds_combine;
    try rewrite (All2_length _ _ _ Haz); trivial.
    rewrite map_map.
    rewrite (map_ext (fun x => snd (fst_map compile x)) snd); try now intros [].
    rewrite snds_combine; try rewrite (All2_length _ _ _ HPs); trivial.
    exact (proj2 Hcomp).
- (* <- *)
  intros Heq As HAs. destruct Hsfa as [_ Hsfa].
  assert (H' : forall aa : pprog,
                 context_has_shape L (map (pair false) PIs ++ map (pair true) AIs)
                                   aa /\
                 comp_compatible L aa
                                 (map_compile
                                    (map Some (combine Ps PIs) ++ repeat None (length AIs))) /\
                 comp_complete
                   (insert aa
                           (map_compile
                              (map Some (combine Ps PIs) ++ repeat None (length AIs)))) ->
                 link
                   (fsts
                      (somes
                         (insert aa
                                 (map_compile
                                    (map Some (combine Ps PIs) ++
                                         repeat None (length AIs)))))) ~~
                   link
                   (fsts
                      (somes
                         (insert aa
                                 (map_compile
                                    (map Some (combine Qs PIs) ++
                                         repeat None (length AIs))))))).
  { clear Hsfa. intros az'.
    unfold fsts, insert, map_compile in *.
    rewrite !map_app, !map_repeat; simpl.
    rewrite !map_map; simpl.
    intros [H1'].
    destruct (context_has_shape_app_l _ _ _ _ H1') as [az'' [az [H1 [H2 H3]]]].
    subst az'. clear H1'.
    apply context_has_shape_false in H2. subst az''.
    apply context_has_shape_true in H3.
    destruct H3 as [aa [? Haa]]. subst az.
    unfold comp_compatible, interfaces_ok.
    rewrite merge_app;
    try rewrite repeat_length, map_length, combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HPs); trivial.
    rewrite <- !(map_map (fst_map compile) Some).
    rewrite merge_None_Some; try rewrite map_length, combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HPs); trivial.
    rewrite merge_app;
    try rewrite repeat_length, !map_length, combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HQs); trivial.
    rewrite merge_Some_None; try rewrite map_length; try rewrite combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ Haa); trivial.
    rewrite merge_None_Some; try rewrite map_length, combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HQs); trivial.
    rewrite !somes_app, !somes_map, !map_app.
    rewrite fsts_combine; try now rewrite (All2_length _ _ _ Haa).
    rewrite !(map_map _ fst).
    rewrite (map_ext (fun x => fst (fst_map compile x)) (fun x => compile (fst x))); try now intros [].
    rewrite <- (map_map fst compile), fsts_combine; try now rewrite (All2_length _ _ _ HPs).
    rewrite (map_ext (fun x => fst (fst_map compile x)) (fun x => compile (fst x))); try now intros [].
    rewrite <- (map_map fst compile), fsts_combine; try now rewrite (All2_length _ _ _ HQs).
    intros [[HAll _] [_ _]]. apply Heq. clear Heq.
    apply All_All2; try now rewrite (All2_length _ _ _ Haa).
    now apply All_app_r in HAll. }
  specialize (Hsfa H'). clear H'.
  specialize (Hsfa (repeat None (length PIs) ++ map Some (combine As AIs))).
  unfold insert in *.
  rewrite merge_app in Hsfa;
  try rewrite repeat_length, map_length, combine_length, min_r; trivial;
  try rewrite (All2_length _ _ _ HPs); trivial.
  rewrite merge_app in Hsfa;
  try rewrite repeat_length, map_length, combine_length, min_r; trivial;
  try rewrite (All2_length _ _ _ HQs); trivial.
  rewrite merge_None_Some in Hsfa;
  try rewrite combine_length, min_r; trivial;
  try rewrite (All2_length _ _ _ HPs); trivial.
  rewrite merge_None_Some in Hsfa;
  try rewrite combine_length, min_r; trivial;
  try rewrite (All2_length _ _ _ HQs); trivial.
  rewrite merge_Some_None in Hsfa;
  try rewrite combine_length, min_r; trivial;
  try rewrite (All2_length _ _ _ HAs); trivial.
  rewrite !somes_app, !somes_map in Hsfa.
  unfold fsts, snds in *.
  rewrite !map_app in Hsfa.
  rewrite fsts_combine in Hsfa; try rewrite (All2_length _ _ _ HPs); trivial.
  rewrite fsts_combine in Hsfa; try rewrite (All2_length _ _ _ HAs); trivial.
  rewrite fsts_combine in Hsfa; try rewrite (All2_length _ _ _ HQs); trivial.
  apply Hsfa. clear Hsfa. repeat split.
  + apply context_has_shape_app.
    * now apply context_has_shape_false_conv.
    * now apply context_has_shape_true_conv.
  + unfold comp_compatible.
    rewrite merge_app; try rewrite repeat_length, map_length, combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HPs); trivial.
    rewrite merge_None_Some; try rewrite combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HPs); trivial.
    rewrite merge_Some_None; try rewrite combine_length, min_r; trivial;
    try rewrite (All2_length _ _ _ HAs); trivial.
    unfold interfaces_ok. rewrite !somes_app, !somes_map.
    unfold snds. rewrite map_app.
    rewrite snds_combine; try now rewrite (All2_length _ _ _ HPs).
    rewrite snds_combine; try now rewrite (All2_length _ _ _ HAs).
    split; try exact (proj1 Hcomp).
    apply All_app; try now apply All2_All.
  + rewrite <- map_app.
    generalize (combine Ps PIs ++ combine As AIs).
    clear.
    now intros Ps; induction Ps as [|P Ps IH]; simpl; intuition.
  + unfold snds.
    rewrite somes_app, !somes_map, map_app, !snds_combine;
    try rewrite (All2_length _ _ _ HPs); trivial;
    try rewrite (All2_length _ _ _ HAs); trivial.
    exact (proj2 Hcomp).
Qed.

End SFAimpliesMD.
