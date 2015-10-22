(* Finite partial maps from nat to T *)
Parameter fpm : forall (T : Set), Set.
Parameter fpm_as_function : forall {T: Set} (m: fpm T), nat -> (unit + T).

(* Languages *)
Parameter (language: Set).
Parameter (component: forall (L: language), Set).
Definition prog (L: language): Set := fpm (component L).
Parameter (link: forall {L: language} (P Q: prog L), prog L).
(* TODO obs becomes beh *)
Parameter (obs_eq: forall {L: language} (P Q: prog L), Prop).

Parameter (compatible: forall {L: language}, prog L -> prog L -> Prop).
Parameter (complete: forall {L: language}, prog L -> Prop).

(* We'll probably need these later *)
(*
Parameter (compatible_merge_yields_program:
             forall {L: language} (P Q : prog L),
               compatible P Q ->
               not (link P Q = inl tt)).
Parameter (obs_eq_implies_complete_left:
             forall {L: language} (P Q : prog L),
               obs_eq P Q -> complete P).
Parameter (obs_eq_implies_complete_right:
             forall {L: language} (P Q : prog L),
               obs_eq P Q -> complete Q).
*)

(* Maybe these as well *)
(*
Hypothesis compatible_implies_disjoint:
  forall (L: language) (P Q: prog L),
    compatible P Q -> fpm_disjoint P Q.
Hypothesis merge_is_disjoint_union:
  forall (L: language) (P Q: prog L) (H: compatible P Q),
    let H' := compatible_implies_disjoint L P Q H in
    merge P Q H = fpm_disjoint_union P Q H'.
*)


Inductive lift1 {L: language} (G: prog L -> Prop) :
  (unit + prog L) -> Prop :=
| lifted1: forall (P: prog L), G P -> lift1 G (inr P).

Inductive lift2 {L: language} (G: prog L -> prog L -> Prop) :
  (unit + prog L) -> (unit + prog L) -> Prop :=
| lifted2: forall (P Q: prog L), G P Q -> lift2 G (inr P) (inr Q).

(* compiler *)
Parameter (src tgt: language).
Parameter compile: prog src -> prog tgt.

Definition statically_indistinguishable {L: language} (P Q: prog L) : Prop :=
  (forall (A: prog L), compatible P A <-> compatible Q A)
  /\
  (forall (A: prog L), compatible P A -> compatible Q A ->
                       lift1 complete (link P A) <-> lift1 complete (link Q A)).
  
Definition dynamically_indistinguishable {L: language} (P Q: prog L) : Prop :=
  forall (A: prog L),
    compatible P A ->
    compatible Q A ->
    lift1 complete (link P A) ->
    lift1 complete (link Q A) ->
    lift2 obs_eq (link P A) (link Q A).

Definition ctx_eq {L: language} (P Q: prog L) : Prop :=
  statically_indistinguishable P Q
  /\
  dynamically_indistinguishable P Q.

Definition full_abstraction: Prop :=
  forall (P Q: prog src),
    ctx_eq P Q <-> ctx_eq (compile P) (compile Q).

(*Parameter domain: forall {T: Set} (m: fpm T), list nat.*)

(*
Lemma : forall P Q, statically_indistinguishable P Q -> same_domain P Q.

Lemma : forall P Q, same_domain P Q -> statically_indistinguishable P Q.
*)

Parameter same_domain: forall {L: language}, prog L -> prog L -> Prop.
Parameter disjoint_domains: forall {L: language}, prog L -> prog L -> Prop.

Definition mutual_distrust_static_eq {L: language} (P Q: prog L) : Prop :=
  same_domain P Q.

Definition mutual_distrust_dynamic_eq {L: language} (P Q: prog L) : Prop :=
  forall (A: prog L),
    
    compatible P A ->
    compatible Q A ->
    lift1 complete (link P A) ->
    lift1 complete (link Q A) ->
    lift2 obs_eq (link P A) (link Q A).

Definition mutual_distrust: Prop :=
  forall (P Q: prog src),
    .

