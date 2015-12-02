(* This was an early attempt at proving that structured full
   abstraction can imply full abstraction, in a specific instance of
   structured full abstraction. *)

(* In this instance, only the attacker gets structure. An unstructured
   program or attacker is a set of components. A structured attacker is
   a set that has a specific cardinal (the cardinal is the shape). *)

(* The (easy) proof is that if we can relate arbitrary attackers of a
   given cardinal, then we can actually relate arbitrary attackers.
   This happens to be true, because all attackers have a cardinal
   (note that attackers are *finite* sets of components). *)

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Class language (component: Type): Type :=
  {
    program: Type;
    beh_eq: relation program;
    beh_eq_Equivalence: Equivalence beh_eq;
    link: Ensemble component -> option program
  }.

Class compiler
      {source_component: Type} {target_component: Type}
      (source: language source_component) (target: language target_component)
: Type :=
  {
    compile: source_component -> target_component
  }.

Parameter source_component: Type.
Parameter target_component: Type.
Parameter source: language source_component.
Parameter target: language target_component.
Parameter C: compiler source target.

Definition fmap {U V: Type} (f: U -> V) (A: Ensemble U): Ensemble V :=
  fun v => (exists u, In _ A u /\ f u = v).

Definition full_abstraction :=
  forall P Q,
  (forall (A: Ensemble source_component) (AP AQ: program),
     Finite _ A ->
     link (Union _ A P) = Some AP ->
     link (Union _ A Q) = Some AQ ->
     beh_eq AP AQ)
  <->
  (forall (a: Ensemble target_component) (aP aQ: program),
     Finite _ a ->
     link (Union _ a (fmap compile P)) = Some aP ->
     link (Union _ a (fmap compile Q)) = Some aQ ->
     beh_eq aP aQ).

Definition full_abstraction_closed_world :=
  forall (n_att: nat) (P Q: Ensemble source_component),
  (forall (A: Ensemble source_component) (AP AQ: program),
     cardinal _ A n_att ->
     link (Union _ A P) = Some AP ->
     link (Union _ A Q) = Some AQ ->
     beh_eq AP AQ)
  <->
  (forall (a: Ensemble target_component) (aP aQ: program),
     cardinal _ a n_att ->
     link (Union _ a (fmap compile P)) = Some aP ->
     link (Union _ a (fmap compile Q)) = Some aQ ->
     beh_eq aP aQ).

Lemma full_abstraction_closed_world_implies_full_abstraction:
  full_abstraction_closed_world -> full_abstraction.
Proof.
  unfold full_abstraction.
  unfold full_abstraction_closed_world.
  intros FACW P Q; split.
  + intros Hhl a aP aQ Hfinitea.
    destruct (finite_cardinal _ a Hfinitea) as [na Hana].
    apply (FACW na P Q); try assumption.
    intros A AP AQ HAna.
    pose (cardinal_finite _ A na HAna) as HfiniteA.
    apply Hhl; try assumption.
  + intros Hll A AP AQ HfiniteA.
    destruct (finite_cardinal _ A HfiniteA) as [nA HAnA].
    apply (FACW nA P Q); try assumption.
    intros a aP aQ HanA.
    pose (cardinal_finite _ a nA HanA) as Hfinitea.
    apply Hll; try assumption.
Qed.
