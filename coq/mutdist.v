Require Import Coq.Lists.List.
Import ListNotations.

Require Import MutualDistrust.fullabst.

Variable perm : nat -> Type.
Variable permute : forall {a:Type} {n:nat}, perm n -> list a -> list a.
(* Coercion permute : perm >-> Funclass. *)

Class interface_language (interface: Type): Type :=
  {
    compatible: list interface -> Prop;
    compatible_cons:
      forall I Is, compatible (I :: Is) -> compatible Is;
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
    link: list component -> program;
    beh_eq: program -> program -> Prop
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

Fixpoint All2 {A B} (P : A -> B -> Prop) l1 l2 : Prop :=
  match l1, l2 with
  | [], [] => True
  | a :: l1', b :: l2' => P a b /\ All2 P l1' l2'
  | _, _ => False
  end.

Definition mutual_distrust
  {interface: Type} {I : interface_language interface}
  {hcomponent hprogram: Type} {lcomponent lprogram: Type}

  (H: component_language I hcomponent hprogram)
  (L: component_language I lcomponent lprogram)
  (compile : hcomponent -> lcomponent) :=

  forall PIs AIs : list interface,
  forall pi : perm (length (PIs++AIs)),
  comp (permute pi (PIs++AIs)) ->
  forall Ps : list hcomponent, All2 has_interface Ps PIs ->
  forall Qs : list hcomponent, All2 has_interface Qs PIs ->
  (forall As : list hcomponent, All2 has_interface As AIs ->
                           link (permute pi (Ps++As))
                        ~~ link (permute pi (Qs++As)))
  <->
  (forall az : list lcomponent, All2 has_interface az AIs ->
                           link (permute pi ((map compile Ps)++az))
                        ~~ link (permute pi ((map compile Qs)++az))).

(* Instantiating structured full abstraction to obtain something
   stronger than mutual distrust (we will use this to prove mutual
   distrust for our compiler) *)

Definition admit {t:Type} : t. Admitted.
Variable isInl : forall {a:Type} {b:Type}, (a+b) -> bool.
Coercion is_true : bool >-> Sortclass. (* Prop *)
Variable fst_map : forall{a b c:Type}, (a->c) -> (a*b) -> (c*b).

Fixpoint somes {A} (l : list (option A)) : list A :=
  match l with
  | [] => []
  | Some a :: l' => a :: somes l'
  | None :: l' => somes l'
  end.

Definition isSome {A} (oa : option A) :=
  match oa with
  | Some _ => true
  | _ => false
  end.

Definition fsts {A B} (l : list (A * B)) : list A :=
  map (@fst _ _) l.

Definition snds {A B} (l : list (A * B)) : list B :=
  map (@snd _ _) l.

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

Definition interfaces_ok (p:pprog) :=
  All (fun PIP => match PIP with (P, IP) => has_interface P IP end) (somes p).

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

Definition program_has_shape (s : shape) (p : pprog) : Prop :=
  context_has_shape (flip_shape s) p.

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

(* AAA: It is a bit strange that [cl_compatible] is a property of [c]
   and [p] separately when in this instance we factor it through
   [merge c p]. This makes it very similar to how we use [cl_complete]
   in e.g. [cl_stat_eq_compatible_complete].  *)

Definition comp_compatible c p :=
  match merge c p with
  | Some cp => interfaces_ok cp /\ compatible (snds (somes cp))
  | None => False
  end.

Definition comp_complete (p : pprog) :=
  (* AAA: interfaces_ok isn't needed here, since it already appears
     in the definition of compatibility *)
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

Instance context_lang_from_component_lang :
     context_language pprog pprog :=
{
  cl_insert := insert;
  cl_compatible := comp_compatible;
  cl_complete := comp_complete;
  cl_stat_eq := stat_eq;
  cl_beh_eq p q := beh_eq (link (fsts (somes p))) (link (fsts (somes q)));

  cl_stat_eq_compatible_complete := _

}.

Proof.
  intros Ps Qs HPsQs As.
  unfold comp_compatible, comp_complete, insert.
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

Instance structured_context_lang_from_component_lang :
     structured_context_language
       context_lang_from_component_lang
       shape :=
{
  scl_context_has_shape := context_has_shape;
  scl_program_has_shape := program_has_shape
}.

End SFAfromMD.

Section SFAimpliesMD.

Context {interface: Type} {I : interface_language interface}
        {hcomponent hprogram: Type} {lcomponent lprogram: Type}
        (H: component_language I hcomponent hprogram)
        (L: component_language I lcomponent lprogram)
        (compile : hcomponent -> lcomponent).

Definition map_compile (p:@pprog interface hcomponent) :
                          @pprog interface lcomponent :=
  List.map (option_map (fst_map compile)) p.

Conjecture sfa_implies_md :
  structured_full_abstraction
    (structured_context_lang_from_component_lang H)
    (structured_context_lang_from_component_lang L)
    map_compile ->
  mutual_distrust H L compile.
(* TODO: prove this *)

End SFAimpliesMD.

Section FAfromMD.

Context {interface: Type} {I: interface_language interface} {component program: Type}.

(* We take both FA programs and contexts to be "partial programs"
   of the following type *)
Definition uprog := list (component*interface).

Definition ucontext :=
  {n:nat & {lc:list (component*interface) & perm (length lc+n)}}%type.

Fixpoint umerge (c:ucontext) (p:uprog) : uprog :=
  let '(existT n (existT lc pi)) := c in
  permute pi (lc ++ p).

Instance unstructured_context_lang_from_component_lang
  (compl : component_language I component program) :
     context_language uprog ucontext :=
{
  cl_insert := umerge;
  cl_compatible c p :=
    let '(existT n (existT lc pi)) := c in
    n = length p /\
    All (fun PIP => match PIP with (P, IP) => has_interface P IP end) (lc++p) /\
    compatible (snds (permute pi (lc ++ p)));
  cl_complete p := complete (snds p);
  cl_stat_eq p q :=
    All2 (fun PIP QIQ =>
            match PIP, QIQ with
              | (P, IP), (Q, IQ) =>
                has_interface P IP /\ has_interface Q IQ /\ IP = IQ
            end) p q;
  cl_beh_eq p q := beh_eq (link (fsts p)) (link (fsts q));
  cl_stat_eq_compatible_complete :=
    admit (* TODO *)
}.

End FAfromMD.

(* TODO: using structured_context_lang_from_component_lang
         and unstructured_context_lang_from_component_lang
         we want to instantiate
         structured_full_abstraction_implies_full_abstraction
*)
