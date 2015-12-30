Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.eqtype Ssreflect.seq.

Require Import Coq.Relations.Relation_Operators.

Require Import MutualDistrust.fullabst.
Require Import MutualDistrust.mutdist.

(* Define RFJ interfaces *)

Parameter component_name: eqType.
Parameter component_signature: eqType.
Parameter signame: component_signature -> component_name.

Record interface: Type :=
  {
    imports: seq component_signature;
    export: component_signature
  }.

(* List the names of the components used in an interface,
   either imported or exported. *)
Definition names (PI: interface): seq component_name :=
  [seq signame sig | sig <- export PI :: imports PI].

(* An interface is self-contained if it only mentions objects and
   classes that are either exported or imported. This is a
   prerequisite for being well-formed. *)
Parameter self_contained: interface -> bool.

Definition well_formed (PI: interface) :=
  uniq (names PI) && self_contained PI.

(* Compatibility of a sequence is defined as pairwise-compatibility,
   where compatibility between two interfaces means the exported name
   is different and there is no conflict on common signatures. *)
Definition rfj_compatible (PIs: seq interface): bool :=
  (* Note that this definition of [no_conflict] is symmetric, so we
     don't need [no_conflict PI' PI] in [compat2]. *)
  let no_conflict PI PI' :=
      all (fun sig =>
             (sig \in export PI' :: imports PI') || (signame sig \notin (names PI'))
          ) (export PI :: imports PI)
  in
  let compat2 PI PI' :=
      (signame (export PI) != signame (export PI')) && no_conflict PI PI'
  in
  all well_formed PIs &&
      (fix f PIs := match PIs with
                      | [::] => true
                      | PI :: PIs' =>
                        all (compat2 PI) PIs' && f PIs'
                    end) PIs.


(* mainsig is:
     component main {
       class {
         main.0(main.0);
       }
       object main.0;
     }
*)
Parameter mainsig: component_signature.
Parameter siginc: component_signature -> component_signature -> bool.

(* A sequence is complete when each imported component name is
   exported by some component, and it has a main component. *)
Definition rfj_complete (PIs: seq interface): bool :=
  let names := [seq signame (export PI) | PI <- PIs] in
  all well_formed PIs &&
      (all (fun PI =>
              all (fun sig =>
                     signame sig \in names
                  ) (imports PI)
           ) PIs) &&
      (has (fun PI => siginc mainsig (export PI)) PIs).

Instance rfji: interface_language interface :=
  {
    compatible := rfj_compatible;
    complete := rfj_complete;
    compatible_cons := _
  }.
Proof.
  move=> I Is.
  move/andP => [H1 H2].
  move/andP :H1 => [_ H12].
  move/andP :H2 => [_ H22].
  (* YJ: "bool_congr." seems buggy on my SSReflect. Any other, better
         way than what's below? *)
  unfold rfj_compatible.
  unfold all.
  rewrite H22.
  rewrite H12.
  reflexivity.
Qed.

(* Define RFJ as a component language *)

Parameter rfj_component_body: eqType.
(* rfj_check_interface includes wellformedness checks *)
Parameter rfj_check_interface: rfj_component_body -> interface -> bool.
Definition rfj_component := (interface * rfj_component_body)%type.
Definition rfj_program := seq rfj_component.
Parameter rfj_beh_eq: rfj_program -> rfj_program -> Prop.

Instance rfj: component_language rfji rfj_component rfj_program :=
  {
    get_interface := fun C =>
                       if rfj_check_interface C.2 C.1 then
                         Some C.1
                       else
                         None;
    link := id;
    beh_eq := rfj_beh_eq
  }.
