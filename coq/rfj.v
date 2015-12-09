Require Import Coq.Lists.List.
Import ListNotations.

Require Import MutualDistrust.fullabst.
Require Import MutualDistrust.mutdist.

(* Define RFJ interfaces *)

Parameter rfj_class_declaration_table: Set.
Parameter rfj_object_declaration_table: Set.

Definition rfj_declaration_table: Set :=
  (rfj_class_declaration_table * rfj_object_declaration_table)%type.

Record rfj_interface: Set :=
  {
    rfj_interface_imports: rfj_declaration_table;
    rfj_interface_exports: rfj_declaration_table
  }.

Parameter rfj_compatible2: rfj_interface -> rfj_interface -> Prop.

Inductive rfj_compatible: list rfj_interface -> Prop :=
| rfj_compatible_nil: rfj_compatible []
| rfj_compatible_cons: forall C Cs,
                         rfj_compatible Cs ->
                         Forall (rfj_compatible2 C) Cs ->
                         rfj_compatible (C :: Cs).

Parameter rfj_complete: list rfj_interface -> Prop.

Instance rfji: interface_language rfj_interface :=
  {
    comp := fun Is => rfj_compatible Is /\ rfj_complete Is
  }.

(* Define RFJ *)

Parameter rfj_class_definition_table: Set.
Parameter rfj_object_definition_table: Set.

Definition rfj_definition_table: Set :=
  (rfj_class_definition_table * rfj_object_definition_table)%type.

Parameter rfj_has_interface:
  rfj_interface -> rfj_definition_table -> Prop.

Record rfj_component: Type :=
  {
    rfj_component_interface: rfj_interface;
    rfj_component_definitions: rfj_definition_table;
    (* restrict to well-formed/well-typed components *)
    rfj_component_wf:
      rfj_has_interface rfj_component_interface rfj_component_definitions
  }.

Definition rfj_program := list rfj_component.

Parameter rfj_beh_eq: rfj_program -> rfj_program -> Prop.

Instance rfj : component_language rfji rfj_component rfj_program :=
  {
    has_interface := fun C I => rfj_component_interface C = I;
    link := id;
    beh_eq := rfj_beh_eq
  }.
