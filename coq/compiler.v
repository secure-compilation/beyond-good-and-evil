Require Import Coq.Lists.List.
Import ListNotations.

Require Import MutualDistrust.language.

Record compiler: Type :=
  {
    source: language;
    target: language;
    compile: @component source -> @component target;
    compile_compatible2:
      forall P Q,
        compatible2 P Q ->
        compatible2 (compile P) (compile Q);
    compile_compatible2_link2:
      forall a P Q,
        compatible2 P Q ->
        compatible2 a (compile (link2 P Q)) ->
        compatible2 a (link2 (compile P) (compile Q));
    compile_complete_link2:
      forall a P Q,
        compatible2 P Q ->
        compatible2 a (compile (link2 P Q)) ->
        compatible2 a (link2 (compile P) (compile Q));
    compile_beh_eq_link2:
      forall a P Q,
        compatible2 P Q ->
        compatible2 a (compile (link2 P Q)) ->
        beh_eq (link2 a (compile (link2 P Q)))
               (link2 a (link2 (compile P) (compile Q)))
  }.

Arguments source {_}.
Arguments target {_}.
Arguments compile {_} _.
Arguments compile_compatible2 {_} _ _ _.
Arguments compile_compatible2_link2 {_} _ _ _ _ _.
Arguments compile_complete_link2 {_} _ _ _ _ _.
Arguments compile_beh_eq_link2 {_} _ _ _ _ _.
