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
    compatible: list interface -> Prop;
    complete: list interface -> Prop
  }.

Let comp
    {interface: Type}
    `{interface_language interface}
    Is := compatible Is /\ complete Is.

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
Variable somes : forall {a:Type}, list (option a) -> list a.
Variable fsts : forall {a:Type} {b:Type}, list (a*b) -> list a.
Variable snds : forall {a:Type} {b:Type}, list (a*b) -> list b.

Section SFAfromMD.

Context {interface: Type} {I: interface_language interface} {component program: Type}.

(* We take both SFA programs and contexts to be "partial programs"
   of the following type *)
Definition pprog := list (option (component*interface)).

(* Need interface equality to decide compatibility? At least in current formulation ... *)
Variable beq_interface : interface -> interface -> bool.

Fixpoint merge_compatible (p:pprog) (q:pprog) : option pprog :=
  match p, q with
  | [], [] => Some []
  | Some (c,i1) :: p', None :: q'
  | None :: p', Some (c,i1) :: q' =>
    match merge_compatible p' q' with
      | Some pq' => Some (Some (c,i1) :: pq')
      | None     => None
    end
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
  cl_compatible c p := match merge_compatible c p with
                         | Some l =>
                           All (fun PIP => match PIP with (P, IP) => has_interface P IP end)
                               (somes l) /\
                           compatible (snds (somes l))
                         | None => False
                       end;
  cl_complete p := All isSome p /\ complete (snds (somes p));
  cl_stat_eq p q :=
    All2 (fun optPIP optQIQ =>
            match optPIP, optQIQ with
              | None, None => True
              | Some (P, IP), Some (Q, IQ) =>
                has_interface P IP /\ has_interface Q IQ /\ IP = IQ
              | _, _ => False
            end) p q;
  cl_beh_eq p q := beh_eq (link (fsts (somes p))) (link (fsts (somes q)));
  cl_stat_eq_compatible_complete :=
    admit (* <-- can't prove this without extra assumptions on comp *)
}.

Definition shape := list (bool*interface). (* replace (bool*interface) with option interface
                                              if dropping scl_program_has_shape *)
Definition flip_shape (s : shape): shape :=
  List.map (fun bi => match bi with (b, i) => (negb b, i) end) s.

Fixpoint context_has_shape (s : shape) (c : pprog) : bool :=
  match s, c with
  | [], [] => true
  | (true,i1)::s', (Some (_,i2))::c' =>
    (* YJ: here, no has_interface check,
           looks OK because it is already in the compatibility check *)
    andb (beq_interface i1 i2) (context_has_shape s' c')
  | (false,_)::s', None::c' =>
    context_has_shape s' c'
  | _, _ => false
  end.

Definition program_has_shape (s : shape) (p : pprog) : bool :=
  context_has_shape (flip_shape s) p.

Instance structured_context_lang_from_component_lang
  (compl : component_language I component program) :
     structured_context_language
       (context_lang_from_component_lang compl)
       shape :=
{
  scl_context_has_shape := context_has_shape;
  scl_program_has_shape := program_has_shape
}.

End SFAfromMD.

Section FAfromMD.

Context {interface: Type} {I: interface_language interface} {component program: Type}.

(* We take both FA programs and contexts to be "partial programs"
   of the following type *)
Definition unstructured_pprog := list (component*interface).

Instance unstructured_context_lang_from_component_lang
  (compl : component_language I component program) :
     context_language unstructured_pprog unstructured_pprog :=
{
  cl_insert c p := c ++ p;
  cl_compatible c p := All (fun PIP => match PIP with (P, IP) => has_interface P IP end)
                           (c ++ p) /\
                       compatible (snds (c ++ p));
  cl_complete p := complete (snds p);
  cl_stat_eq p q :=
    All2 (fun PIP QIQ =>
            match PIP, QIQ with
              | (P, IP), (Q, IQ) =>
                has_interface P IP /\ has_interface Q IQ /\ IP = IQ
            end) p q;
  cl_beh_eq p q := beh_eq (link (fsts p)) (link (fsts q));
  cl_stat_eq_compatible_complete :=
    admit (* <-- can't prove this without extra assumptions on comp *)
}.

End FAfromMD.
