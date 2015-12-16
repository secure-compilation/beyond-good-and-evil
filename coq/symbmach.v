Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Relations.Relation_Operators.

Require Import MutualDistrust.fullabst.
Require Import MutualDistrust.mutdist.
Require Import MutualDistrust.rfj.

(* Define symbolic machine programs as a component language *)

(* Components are not tagged: tags are provided by the linker *)
Parameter symb_mem_word: Set.
Parameter symb_mem_loc: Set.
Definition symb_mem_region := list symb_mem_word.
Definition symb_prog := list (symb_mem_loc * symb_mem_region).
Definition symb_component := (rfj_interface * symb_prog)%type.

(* The linker sets tags *)
Parameter symb_mem_tag: Set.
Definition symb_mem_tagged_region := list (symb_mem_word * symb_mem_tag).
Definition symb_tagged_prog := list (symb_mem_loc * symb_mem_tagged_region).
Parameter symb_linker: list symb_component -> symb_tagged_prog.

(* The loader takes the result of the linker to a machine state. *)
Parameter symb_machine_state: Set.
Parameter symb_reduce: symb_machine_state -> symb_machine_state -> Prop.
Parameter symb_loader: symb_tagged_prog -> symb_machine_state.
Coercion symb_loader: symb_tagged_prog >-> symb_machine_state.

Notation "s --> s'" := (symb_reduce s s') (at level 50, no associativity).
Notation "s -/-> s'" := (~ symb_reduce s s') (at level 50, no associativity).
Notation "s -->* s'" := (clos_refl_trans _ symb_reduce s s')
                        (at level 50, no associativity).

Definition symb_stuck (s: symb_machine_state): Prop :=
  forall (s': symb_machine_state), s -/-> s'.

Definition symb_terminates (s: symb_machine_state) :=
  exists s', s -->* s' /\ symb_stuck s'.

Parameter symb_prog_has_interface : symb_prog -> rfj_interface -> Prop.
(* The program should define memory regions only for the components *)
(* mentioned in the interface. When a location is missing, the *)
(* corresponding memory regions will be filled with zeros and *)
(* tagged. *)

Instance symb_machine : component_language rfji symb_component symb_tagged_prog :=
  {
    has_interface := fun C I => fst C = I /\ symb_prog_has_interface (snd C) I;
    link := symb_linker;
    beh_eq := fun P Q => (symb_terminates P <-> symb_terminates Q)
  }.
