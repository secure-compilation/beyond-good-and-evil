Require Import Coq.Lists.List.
Import ListNotations.

(** This function is available on 8.5, but not on 8.4 *)

Fixpoint repeat {A} (x : A) (n : nat) : list A :=
  match n with
  | 0 => []
  | S n' => x :: repeat x n'
  end.

Lemma repeat_length {A} (x : A) n : length (repeat x n) = n.
Proof. now induction n as [|n IH]; simpl; trivial; rewrite IH. Qed.
