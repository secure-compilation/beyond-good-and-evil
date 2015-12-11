Require Import Coq.Lists.List.
Import ListNotations.

Require Import MutualDistrust.fullabst.
Require Import MutualDistrust.mutdist.
Require Import MutualDistrust.rfj.

Definition admit {t:Type} : t. Admitted.

(* Define symbolic machine programs as a component language *)

Parameter mem_word: Set.
Parameter mem_tag: Set.

Definition component_id := nat.
Definition class_id := nat.
Definition meth_id := nat.
Definition obj_id := nat.

Inductive mem_loc: Set :=
| stackl : component_id -> mem_loc
| methl : component_id -> class_id -> meth_id -> mem_loc
| objl : component_id -> class_id -> obj_id -> mem_loc.

(* Untagged symbolic programs *)

Definition mem_region := list mem_word.

Definition symb_prog := list (mem_loc * mem_region).

(* Tagged symbolic programs *)

Definition tagged_mem_region := list (mem_word * mem_tag).

Definition tagged_symb_prog := list (mem_loc * tagged_mem_region).

(* Components *)

Definition symb_component := (rfj_interface * symb_prog)%type.

(* Restricts the mem_locs to components that appear in rfj_interface *)
Definition symb_prog_has_interface: symb_prog -> rfj_interface -> Prop :=
  (* the program should define memory regions only for the components mentionned in the interface *)

  (* when a location is missing, the corresponding memory regions will be filled with zeros and tagged *)
  admit.

(* Apply loader then look for equitermination. *)
Instance symb_machine : component_language rfji symb_component tagged_symb_prog.
Admitted.
