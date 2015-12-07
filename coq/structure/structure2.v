Require Import Coq.Unicode.Utf8.

Section FA.

(** We assume that we have two languages: a source language (denoted
by "src") and a target language (denoted by "tgt"). Both languages
have a notion of program and context; the latter should be thought of
as a program that has holes that can be filled in, with the
[*_ctx_app] functions. Notice that we add coercions to allow us to use
function application syntax to apply a context to a program. *)

Variable src_prog src_ctx : Type.
Variable src_ctx_app : src_ctx → src_prog → src_prog.
Coercion src_ctx_app : src_ctx >-> Funclass.

Variable tgt_prog tgt_ctx : Type.
Variable tgt_ctx_app : tgt_ctx → tgt_prog → tgt_prog.
Coercion tgt_ctx_app : tgt_ctx >-> Funclass.

(** We assume that the source language is _typed_. We use the types to
specify when two programs have compatible signatures (which is close
to the notion of "static equivalence"). We also use types to indicate
which contexts can be used with a certain program: if [⊢ p ∈ t], we
only want to consider contexts [ctx] that satisfy [takes_type ctx
t]. Here, we consider such contexts to be _compatible_ with the
program [p], and that applying a context to a compatible program
results in a complete program that can be run. *)

Variable type : Type.

Variable has_type : src_prog → type → Prop.
Notation "⊢ p ∈ t" := (has_type p t)
  (at level 0, format "⊢  p  ∈  t").

Variable takes_type : src_ctx → type → Prop.

(** We assume two notions of program equivalence (for the source and
target languages) and a compilation function. We do not state any
hypotheses that need to be satisfied by them. *)

Variable src_eq : src_prog → src_prog → Prop.
Notation "p ≡_s q" := (src_eq p q)
  (at level 60, no associativity).

Variable tgt_eq : tgt_prog → tgt_prog → Prop.
Notation "p ≡_t q" := (tgt_eq p q)
  (at level 60, no associativity).

Variable compile : src_prog → tgt_prog.
Notation "p ↓" := (compile p)
  (at level 0, format "p ↓").

(** The usual definition of full abstraction. Notice that we only try
to equate programs at the source level when applied to contexts whose
type matches the one of the programs we are considering. *)

Definition full_abstraction : Prop :=
  ∀ p q t,
    ⊢ p ∈ t →
    ⊢ q ∈ t →
    (∀ ctx : src_ctx,
       takes_type ctx t → ctx p ≡_s ctx q)
    ↔
    (∀ ctx : tgt_ctx, ctx p↓ ≡_t ctx q↓).

(* CH: takes_type only at the high-level; why asymmetric? Would this
   work at all in our setting? Arthur agrees now that's not good.*)
(* CH: static equivalence replaced by "having same type" *)

(** To state structured full abstraction, we assume a type of shapes
that we can use to classify source and target contexts. Each context
has a corresponding shape, which can be computed with the [*_shape]
functions. Notice that this departs from the original development,
which relates contexts and shapes via a predicate. Intuitively, this
means that our type of contexts only includes contexts that have a
well-defined shape. Besides that, we do not assume that the programs
that are plugged into a context need to be related to the shape of
that context in any way. *)

Variable shape : Type.
Variable src_shape : src_ctx → shape.
Variable tgt_shape : tgt_ctx → shape.

(** The definition of structured full abstraction. Intuitively, it
says that, if there is a target context [ctx] that can distinguish
between two compiled programs [p↓] and [q↓], then there should be a
source-level context [ctx'] of the _same_ shape as [ctx] that can
distinguish [p] and [q]. *)

Definition structured_full_abstraction : Prop :=
  ∀ p q t s,
    ⊢ p ∈ t →
    ⊢ q ∈ t →
    (∀ ctx : src_ctx,
       takes_type ctx t →
       src_shape ctx = s →
       ctx p ≡_s ctx q)
    ↔
    (∀ ctx : tgt_ctx,
       tgt_shape ctx = s →
       ctx p↓ ≡_t ctx q↓).

(* CH: shape not related to program, so p and q could have different
       shapes, which is very bad? unless the type / static
       equivalent takes care of that part? TODO: think about this *)

(* CH: using the same programs, typing, equivalence but restricting
       only shapes could be a reasonable simplification? It basically
       makes the implication below almost trivial; the only thing
       that's left is the original intuition that we can turn contexts
       into shapes. TODO: think about this *)

(** As expected, the structured variant is stronger that the
unstructured one.

It seems that if we wanted to find a program where the unstructured
variant is not enough, we would have to find two programs that cannot
be distinguished by contexts of a certain shape [s₁], but _can_ be
distinguished if we allow contexts of a shape [s₂]. If we take "shape"
in our setting to mean something like "the number of compartments that
appear in the context, plus how they are allowed to interact", then it
seems that the example I included on "mutdist.org" indeed requires the
structured variant, since we must assume that the context contains two
compartments that are not allowed to communicate. *)

Theorem structured_implies_unstructured :
  structured_full_abstraction →
  full_abstraction.
Proof.
intros sfa p q t p_t q_t; split.
- intros Heq ctx.
  now apply (sfa p q t (tgt_shape ctx) p_t q_t); eauto.
- intros Heq ctx ctx_t.
  now apply (sfa p q t (src_shape ctx) p_t q_t); eauto.
Qed.

End FA.
