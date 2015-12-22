Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.eqtype Ssreflect.seq.

Require Import Coq.Relations.Relation_Operators.

Require Import MutualDistrust.fullabst.
Require Import MutualDistrust.mutdist.

(* Define RFJ interfaces *)

Parameter component_name: eqType.
Parameter component_signature: eqType.

Record interface: Type :=
  {
    imports: seq (component_name * component_signature);
    export: component_name * component_signature
  }.

Definition names (PI: interface): seq component_name :=
  [seq name_sig.1 | name_sig <- export PI :: imports PI].

Definition well_formed (PI: interface): bool :=
  uniq (names PI).

Definition rfj_compatible2_split (PI PI': interface): bool :=
  (export PI \in imports PI') || ((export PI).1 \notin (names PI')).

Definition rfj_compatible2 (PI PI': interface): bool :=
  (rfj_compatible2_split PI PI') && (rfj_compatible2_split PI' PI).

Fixpoint rfj_compatible (PIs: list interface): bool :=
  (match PIs with
     | [::] => true
     | PI :: PIs' =>
       (all well_formed PIs &&
        all (rfj_compatible2 PI) PIs') &&
       rfj_compatible PIs'
     end).

Definition rfj_complete (PIs: seq interface): bool :=
  let names := [seq (export PI).1 | PI <- PIs] in
  andb (all well_formed PIs)
       (all (fun PI => all (fun name_sig => name_sig.1 \in names) (imports PI)) PIs).

Instance rfji: interface_language interface :=
  {
    compatible := rfj_compatible;
    complete := rfj_complete;
    compatible_cons := _
  }.
Proof.
  move=> I Is.
  by move/andP => [_ H].
Qed.

(* Define RFJ as a component language *)

Parameter rfj_component_body: eqType.
Parameter rfj_check_interface: rfj_component_body -> interface -> bool.
Definition rfj_component :=
  ((component_name * component_signature) * rfj_component_body)%type.
Definition rfj_program := seq rfj_component.
Parameter rfj_beh_eq: rfj_program -> rfj_program -> Prop.

Instance rfj: component_language rfji (interface * rfj_component_body) rfj_program :=
  {
    get_interface := fun C =>
                       if rfj_check_interface C.2 C.1 then
                         Some C.1
                       else
                         None;
    link := fun Cs => [seq (export C.1, C.2) | C <- Cs];
    beh_eq := rfj_beh_eq
  }.
