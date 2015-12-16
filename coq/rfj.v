Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Relations.Relation_Operators.

Require Import MutualDistrust.fullabst.
Require Import MutualDistrust.mutdist.

(* Define RFJ interfaces *)

Parameter rfj_interface: Set.
Parameter rfj_compatible2: rfj_interface -> rfj_interface -> Prop.
(* Compatibility is pair-wise compatibility. *)
Inductive rfj_compatible: list rfj_interface -> Prop :=
| rfj_compatible_nil: rfj_compatible []
| rfj_compatible_cons: forall C Cs,
                         rfj_compatible Cs ->
                         Forall (rfj_compatible2 C) Cs ->
                         rfj_compatible (C :: Cs).
Parameter rfj_complete: list rfj_interface -> Prop.

Lemma rfj_compatible_cons_inv:
  forall I Is, rfj_compatible (I :: Is) -> rfj_compatible Is.
Proof.
  intros I Is H.
  now inversion H.
Qed.

Instance rfji: interface_language rfj_interface :=
  {
    compatible := rfj_compatible;
    compatible_cons := rfj_compatible_cons_inv;
    complete := rfj_complete
  }.

(* Define RFJ as a component language *)

Parameter rfj_defs: Set.
Definition rfj_component: Set := (rfj_interface * rfj_defs)%type.
Definition rfj_program := list rfj_component.
Parameter rfj_beh_eq: rfj_program -> rfj_program -> Prop.

Parameter rfj_has_interface: rfj_defs -> rfj_interface -> Prop.

Instance rfj: component_language rfji rfj_component rfj_program :=
  {
    has_interface := fun C I => fst C = I /\ rfj_has_interface (snd C) I;
    link := id;
    beh_eq := rfj_beh_eq
  }.
