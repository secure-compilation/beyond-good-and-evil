Require Import Coq.Lists.List.
Import ListNotations.

Require Import MutualDistrust.fullabst.
Require Import MutualDistrust.mutdist.

(* Define RFJ *)

Parameter rfj_class_declaration_table: Set.
Parameter rfj_object_declaration_table: Set.
Parameter rfj_class_definition_table: Set.
Parameter rfj_object_definition_table: Set.

Definition rfj_declaration_table: Set :=
  (rfj_class_declaration_table * rfj_object_declaration_table)%type.
Definition rfj_definition_table: Set :=
  (rfj_class_definition_table * rfj_object_definition_table)%type.

Parameter has_interface:
  rfj_declaration_table -> rfj_definition_table -> rfj_declaration_table -> Prop.

Record rfj_component: Type :=
  {
    rfj_component_imports: rfj_declaration_table;
    rfj_component_exports: rfj_declaration_table;
    rfj_component_definitions: rfj_definition_table;
    rfj_component_wf:
      has_interface rfj_component_imports rfj_component_definitions rfj_component_exports
  }.

Parameter rfj_compatible2: rfj_component -> rfj_component -> Prop.

Inductive rfj_compatible: list rfj_component -> Prop :=
| rfj_compatible_nil: rfj_compatible []
| rfj_compatible_cons: forall C Cs,
                         rfj_compatible Cs ->
                         Forall (rfj_compatible2 C) Cs ->
                         rfj_compatible (C :: Cs).

Definition rfj_program := list rfj_component.

Parameter rfj_complete: rfj_program -> Prop.

Parameter rfj_beh_eq: rfj_program -> rfj_program -> Prop.

(*
Instance rfj : component_language rfj_component rfj_program :=
  {
    compatible := rfj_compatible;
    complete := rfj_complete;
    link := @id rfj_program;
    beh_eq := rfj_beh_eq
  }.*)
