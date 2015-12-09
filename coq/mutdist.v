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

(* Instantiating structured full abstraction to obtain something
   stronger than mutual distrust (we will use this to prove mutual
   distrust for our compiler) *)

Definition admit {t:Type} : t. Admitted.
Variable All : forall {a:Type} (P:a->Prop), list a -> Prop.
Variable isInl : forall {a:Type} {b:Type}, (a+b) -> bool.
Variable isSome : forall {a:Type}, option a -> bool.
Coercion is_true : bool >-> Sortclass. (* Prop *)
Variable inls : forall {a:Type} {b:Type}, list (a+b) -> list a.
Variable inrs : forall {a:Type} {b:Type}, list (a+b) -> list b.
Variable fsts : forall {a:Type} {b:Type}, list (a*b) -> list a.

Section SFAfromMD.

Context {interface: Type} {I: interface_language interface} {component program: Type}.

(* We take both SFA programs and contexts to be "partial programs"
   of the following type *)
Definition pprog := list ((component*interface) + interface).

(* Need interface equality to decide compatibility? At least in current formulation ... *)
Variable beq_interface : interface -> interface -> bool.

Fixpoint merge_compatible (p:pprog) (q:pprog) : option pprog :=
  match p, q with
  | [], [] => Some []
  | inl (c,i1) :: p', inr i2 :: q'
  | inr i2 :: p', inl (c,i1) :: q' =>
      if beq_interface i1 i2 then
        match merge_compatible p' q' with
        | Some pq' => Some (inl (c,i1) :: pq')
        | None     => None
        end
      else None
  | _, _ => None
  end.

Instance context_lang_from_component_lang 
  (compl : component_language I component program) :
     context_language pprog pprog :=
{
  cl_insert c p := match merge_compatible c p with
                   | Some cp => cp
                   | None    => [] (* shouldn't happen *)
                   end;
  cl_compatible c p := isSome (merge_compatible c p);
  cl_complete p := All isInl p;
  cl_stat_eq p q := comp (inrs p ++ inrs q);
  cl_beh_eq p q := beh_eq (link (fsts (inls p))) (link (fsts (inls q)));
  cl_stat_eq_compatible_complete :=
    admit (* <-- can't prove this without extra assumptions on comp *)
}.

Fixpoint context_has_shape (s : list (bool*interface)) (c : pprog) : bool :=
  match s, c with
  | [], [] => true
  | (true,i1)::s', (inl (_,i2))::c'
  | (false,i1)::s', (inr i2)::c'
     => andb (beq_interface i1 i2) (context_has_shape s' c')
  | _, _ => false
  end.

Instance structured_context_lang_from_component_lang 
  (compl : component_language I component program) :
     structured_context_language
       (context_lang_from_component_lang compl)
       (list (bool*interface)) := (* replace (bool*interface) with option interface
                                  if dropping scl_program_has_shape *)
{
  scl_context_has_shape := context_has_shape;
  scl_program_has_shape s p := admit (* the same, just flip all bools *)
}.
