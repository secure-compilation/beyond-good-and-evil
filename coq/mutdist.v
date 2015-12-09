Require Import Coq.Lists.List.
Import ListNotations.

Require Import MutualDistrust.fullabst.

Variable perm : nat -> Type.
Variable permute : forall {a:Type} {n:nat}, perm n -> list a -> list a.
(* Coercion permute : perm >-> Funclass. *)

Variable All2 : forall {a:Type} {b:Type} (P:a->b->Prop), list a -> list b -> Prop.
(* Print Forall. -- Adam defines this as fixpoint *)

Class interface_language (interface: Type): Type :=
  {
    comp: list interface -> Prop (* compatible and complete *)
  }.

Class component_language
      {interface: Type} (il: interface_language interface)
      (component: Type) (program: Type): Type :=
  {
    has_interface : component -> interface -> Prop;
    link: list component -> program;
    beh_eq: program -> program -> Prop
  }.

Notation "P ~~ Q" := (beh_eq P Q) (at level 60, no associativity).

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

(*Instance unstructured_components : context_language (finset component) (finset component) :=
  {
    cl_insert := union component;
    cl_compatible := compatible;
      cl_complete := fun P => complete (link P);
      cl_stat_eq := fun P Q => forall A, compatible (A P);
         cl_beh_eq: cl_program -> cl_program -> Prop;
         cl_stat_eq_compatible_complete:
      forall P Q,
        cl_stat_eq P Q ->
        (forall A,
           cl_compatible A P /\ cl_complete (cl_insert A P) ->
           cl_compatible A Q /\ cl_complete (cl_insert A Q))

  }.
*)