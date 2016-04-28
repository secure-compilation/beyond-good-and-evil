Require Export SfLib.

(* _____________________________________ 
                  SYNTAX  
   _____________________________________ *)

Definition component := nat.
Definition procedure := nat.
Definition buffer := nat.

Inductive binop : Type :=
  | EEq
  | ELeq
  | ESeq
  | EAdd
  | EMinus
  | EMul.

Inductive expr : Type :=
  | EVal : nat -> expr (* i *)
  | EBinop : binop -> expr -> expr -> expr (* e₁ ⊗ e₂ *)
  | EIfThenElse : expr -> expr -> expr -> expr (* if e then e₁ else e₂ *)
  | ELoad : buffer -> expr -> expr (* b[e] *)
  | EStore : buffer -> expr -> expr -> expr (* b[e] := e *)
  | ECall : component -> procedure -> expr -> expr (* C.P(e) *)
  | EExit : expr. (* exit *)

Definition eval_binop (e : binop * nat * nat) : expr :=
  match e with
  | (EEq, a, b) => if (beq_nat a b) then EVal 1 else EVal 0
  | (ELeq, a, b) => if (ble_nat a b) then EVal 1 else EVal 0
  | (ESeq, a, b) => EVal b
  | (EAdd, a, b) => EVal (a+b)
  | (EMinus, a, b) => EVal (a-b)
  | (EMul, a, b) => EVal (a*b)
  end.

(* ------- Notations : main instructions ------- *)

Notation "'IFB' e1 'THEN' e2 'ELSE' e3" :=
  (EIfThenElse e1 e2 e3) (at level 80, right associativity).
Notation "'LOAD' b << e >>" :=
  (ELoad b e) (at level 0).
Notation "'STORE' e2 'IN' b << e1 >>" :=
  (EStore b e1 e2) (at level 60).
Notation "'CALL' C ':::' P 'WITH' e" :=
  (ECall C P e) (at level 50).
Notation "'exit'" :=
  EExit.

(* ------- Notations : binary operators ------- *)

Notation "e1 ;; e2" :=
  (EBinop ESeq e1 e2) (at level 80, right associativity). 
Notation "e1 == e2" :=
  (EBinop EEq e1 e2) (at level 80, right associativity).


(* _____________________________________ 
           OPERATIONAL SEMANTICS
   _____________________________________ *)

(* ------- Syntax for terms in a context ------- *)

Inductive flatevalcon : Type :=
  | CHoleOp : binop -> expr -> flatevalcon (* □ ⊗ e₂ *)
  | COpHole : nat -> binop -> flatevalcon (* i₁ ⊗ □ *)
  | CIfHoleThenElse : expr -> expr -> flatevalcon (* if □ then e₁ else e₂ *)
  | CHoleLoad : nat -> flatevalcon (* b[□] *)
  | CHoleStore : nat -> expr -> flatevalcon (* b[□] := e *)
  | CStoreHole : nat -> nat -> flatevalcon (* b[i] := □ *)
  | CCallHole : nat -> nat -> flatevalcon. (* C.P(□) *)

(* ------- Notations : terms in a context ------- *)

Notation "'IFB' □ 'THEN' e1 'ELSE' e2" :=
  (CIfHoleThenElse e1 e2) (at level 80, right associativity).
Notation "'LOAD' b << □ >>" :=
  (CHoleLoad b) (at level 0).
Notation "'STORE' e 'IN' b << □ >>" := 
  (CHoleStore b e) (at level 60).
Notation "'STORE' □ 'IN' b << i >>" :=
  (CStoreHole b i) (at level 60).
Notation "'CALL' C ':::' P 'WITH' □" :=
  (CCallHole C P) (at level 50).

(* ------- Definitions : datatypes ------- *)

Definition continuations :=
  list flatevalcon.

Inductive call : Type :=
  | Call : component -> nat -> continuations -> call.

Definition callStack :=
  list call.

Definition state :=
  list (list (list nat)).

Definition fetch_state (C:component) (b:buffer) (i:nat) (s:state) :=
  nth i (nth b (nth C s []) []) 0.

Fixpoint update_value
  (i:nat) (i':nat) (l:list nat) : list nat :=
  match l with
  | [] => [] 
  | h::t => match i with
            | 0 => i'::t
            | S n => h :: (update_value n i' t)
            end
  end.

Fixpoint update_buffer 
  (b:buffer) (i:nat) (i':nat) (l:list (list nat)) : list (list nat) :=
  match l with
  | [] => []
  | h::t => match b with
            | 0 => (update_value i i' h) :: t
            | S b' => h::(update_buffer b' i i' t)
            end
  end.

Fixpoint update_component
  (C:component) (b:buffer) (i:nat) (i':nat) (s:state) : state :=
  match s with
  | [] => []
  | h::t => match C with
            | 0 => (update_buffer b i i' h) :: t
            | S C' => h::(update_component C' b i i' t)
            end 
  end.

Definition update_state
  (C:component) (b:buffer) (i:nat) (i':nat) (s:state) : state :=
  update_component C b i i' s.

Definition cfg : Type :=
  component * state * callStack * continuations * expr.

Definition context :=
  list (list expr).

Definition fetch_context 
  (C':component) (P':procedure) (D:context) : expr :=
  nth P' (nth C' D []) exit.

Definition main_cid := 0.

Definition initial_cfg (D:context) (s:state) : cfg :=
  (main_cid, (update_state main_cid 0 0 0 s), [], [], (fetch_context main_cid 0 D)).

Inductive final_cfg : cfg -> Prop :=
  | final_value : forall C s i, final_cfg (C, s, [], [], EVal i)
  | final_exit  : forall C s d K, final_cfg (C, s, d, K, EExit). 

(* ------- Definitions : small-step semantic definition ------- *)

Reserved Notation "D ⊢ e '⇒' e'" (at level 40).
Inductive small_step (D: context) : cfg -> cfg -> Prop :=
  | S_BinOp_Push : forall C s d K e1 e2 op,
    D ⊢ (C, s, d, K, EBinop op e1 e2) ⇒
    (C, s, d, (CHoleOp op e2)::K, e1)
  | S_BinOp_Switch : forall C s d e2 K i1 op,
    D ⊢ (C, s, d, (CHoleOp op e2)::K, EVal i1) ⇒
    (C, s, d, (COpHole i1 op)::K, e2)
  | S_BinOp_Pop : forall C s d i1 op K i2,
    D ⊢ (C, s, d, (COpHole i1 op)::K, EVal i2) ⇒
    (C, s, d, K, eval_binop (op, i1, i2))
  | S_If_Push : forall C s d K e e1 e2,
    D ⊢ (C, s, d, K, (IFB e THEN e1 ELSE e2)) ⇒
    (C, s, d, (IFB □ THEN e1 ELSE e2)::K, e)
  | S_If_Pop_NZ : forall C s d K e1 e2 i,
    ~(i=0) -> D ⊢ (C, s, d, (IFB □ THEN e1 ELSE e2)::K, EVal i) ⇒
    (C, s, d, K, e1)
  | S_If_Pop_Z : forall C s d e1 e2 K,
    D ⊢ (C, s, d, (IFB □ THEN e1 ELSE e2)::K, EVal 0) ⇒
    (C, s, d, K, e2)
  | S_Read_Push : forall C s d K b e,
    D ⊢ (C, s, d, K, ELoad b e) ⇒
    (C, s, d, (CHoleLoad b)::K, e)
  | S_Read_Pop : forall C s d b K i,
    D ⊢ (C, s, d, (CHoleLoad b)::K, EVal i) ⇒
    (C, s, d, K, EVal (fetch_state C b i s))
  | S_Write_Push : forall C s d K b e1 e2,
    D ⊢ (C, s, d, K, EStore b e1 e2) ⇒
    (C, s, d, (CHoleStore b e2)::K, e1)
  | S_Write_Swap : forall C s d b e2 K i,
    D ⊢ (C, s, d, (CHoleStore b e2)::K, EVal i) ⇒
    (C, s, d, (CStoreHole b i)::K, e2)
  | S_Write_Pop : forall C s d b i K i',
    D ⊢ (C, s, d, (CStoreHole b i)::K, EVal i') ⇒
    (C, (update_state C b i i' s), d, K, EVal i')
  | S_Call_Push : forall C s d K C' P' e,
    D ⊢ (C, s, d, K, ECall C' P' e) ⇒
    (C, s, d, (CCallHole C' P')::K, e)
  | S_Call_Pop : forall C' P' ep C s d K ia,
    (fetch_context C' P' D) = ep ->     
    D ⊢ (C, s, d, (CCallHole C' P')::K, EVal ia) ⇒
    (C', (update_state C' 0 0 ia s), (Call C (fetch_state C 0 0 s) K)::d, [], ep)
  | S_Return : forall C s C' ia K d i,
    D ⊢ (C, s, (Call C' ia K)::d, [], EVal i) ⇒
    (C', (update_state C' 0 0 ia s), d, K, EVal i)
  where "D ⊢ e '⇒' e'" := (small_step D e e').

(* ------- Definitions : small-step multi-reduction ------- *)

Inductive multi {X:Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation "D ⊢ e '⇒*' e'" := (multi (small_step D) e e') (at level 40).


(* _____________________________________ 
           EVALUATION FUNCTION
   _____________________________________ *)

Definition basic_eval_cfg (D:context) (c:cfg) : cfg :=
  match c with
  | (C, s, d, K, EBinop op e1 e2) => 
    (C, s, d, (CHoleOp op e2) :: K, e1)
  | (C, s, d, (CHoleOp op e2) :: K, EVal i1) =>
    (C, s, d, (COpHole i1 op) :: K, e2)
  | (C, s, d, (COpHole i1 op) :: K, EVal i2) =>
    (C, s, d, K, (eval_binop (op, i1, i2)))
  | (C, s, d, K, (EIfThenElse e1 e2 e3)) =>
    (C, s, d, (CIfHoleThenElse e2 e3) :: K, e1)
  | (C, s, d, (CIfHoleThenElse e2 e3) :: K, EVal 0) =>
    (C, s, d, K, e3)
  | (C, s, d, (CIfHoleThenElse e2 e3) :: K, EVal _) =>
    (C, s, d, K, e2)
  | (C, s, d, K, (ELoad b e)) =>
    (C, s, d, (CHoleLoad b) :: K, e)
  | (C, s, d, (CHoleLoad b) :: K, EVal i) =>
    (C, s, d, K, EVal (fetch_state C b i s))
  | (C, s, d, K, (EStore b e1 e2)) =>
    (C, s, d, (CHoleStore b e2) :: K, e1)
  | (C, s, d, (CHoleStore b e2) :: K, EVal i1) =>
    (C, s, d, (CStoreHole b i1) :: K, e2)
  | (C, s, d, (CStoreHole b i1) :: K, EVal i2) =>
    (C, update_state C b i1 i2 s, d, K, EVal i2)
  | (C, s, d, K, (ECall C' P' e)) =>
    (C, s, d, (CCallHole C' P') :: K, e)
  | (C, s, d, (CCallHole C' P') :: K, EVal i) =>
    (C', (update_state C' 0 0 i s), ((Call C (fetch_state C 0 0 s) K) :: d), [], (fetch_context C' P' D))
  | (C, s, (Call C' ia K) :: d', [], EVal i) =>
    (C', update_state C' 0 0 ia s, d', K, EVal i)
  | (_, _, [], [], EVal _) => c
  | (_, _, _, _, EExit) => c
  end.

(* We define a maximum number of reductions because we can write
infinite recursion and Coq doesn't allows non-terminating functions*)
Fixpoint eval_cfg (D:context) (c:cfg) (limit:nat) : cfg :=
  match limit with
  | 0 => c
  | S n => 
    match c with
    | (_, _, [], [], EVal _) => c
    | (_, _, _, _, EExit) => c
    | c' => eval_cfg D (basic_eval_cfg D c') n
    end
  end.


(* _____________________________________ 
       EXAMPLES / SANITY CHECKING
   _____________________________________ *)

(* ------- Fetch state ------- *)

Definition state1 : state :=
  [ 
    (* Component 0 *)
    [
      (* Buffer 0 *)
      [0;1;2;3] ;
      (* Buffer 1 *)
      [4;5;6;7]
    ] 
    ;
    (* Component 1 *)
    [
      (* Buffer 0 *)
      [8;9;10;11] ;
      (* Buffer 1 *)
      [12;13;14;15]
    ]
  ].

Eval compute in (
  update_state 1 0 0 6 state1
).

(* ------- Factorial computation ------- *)

Definition context_fact : context :=
  [
    (* C0 *)
    [
      (exit);
      (exit)
    ];

    (* C1 *)
    [
      (
        IFB (EBinop ELeq (LOAD 0<<EVal 0>>) (EVal 1)) THEN
          EVal 1
        ELSE
          EBinop EMul 
        (CALL 1:::0 WITH (EBinop EMinus LOAD 0<<EVal 0>> (EVal 1))) (LOAD 0<<EVal 0>>)
      );
      (exit)
    ];

    (* C2 *)
    [
      (exit);
      (exit)
    ]
  ].

Eval compute in (fetch_context 1 0 context_fact).

Definition state_fact : state :=
  [ 
    (* Component 0 *)
    [
      (* Buffer 0 *)
      [0;0;0;0] ;
      (* Buffer 1 *)
      [0;0;0;0]
    ] 
    ;
    (* Component 1 *)
    [
      (* Buffer 0 *)
      [0;0;0;0] ;
      (* Buffer 1 *)
      [0;0;0;0]
    ]
  ].

Definition recursive_factorial : expr :=
  fetch_context 1 0 context_fact.

Definition factorial_2 : expr :=
  CALL 1:::0 WITH EVal 2.

Tactic Notation "subcompute" constr(t) :=
  set (_x := t); compute in _x; unfold _x; clear _x.

Eval compute in (eval_cfg context_fact (1, state_fact, [], [], factorial_2) 1000).

Example fact_2_eval :
  context_fact ⊢ (1, state_fact, [], [], factorial_2) ⇒* 
  (1, state_fact, [], [], EVal 2).
Proof.
  unfold factorial_2.
  eapply multi_step. apply S_Call_Push.
  eapply multi_step. apply S_Call_Pop. reflexivity.
  eapply multi_step.
    subcompute (fetch_context 1 0 context_fact).
    apply S_If_Push.
  eapply multi_step. apply S_BinOp_Push. 
  eapply multi_step. apply S_Read_Push.
  eapply multi_step. apply S_Read_Pop.
  eapply multi_step.
    subcompute (EVal (fetch_state 1 0 0 (update_state 1 0 0 2 state_fact))).
    apply S_BinOp_Switch.
  eapply multi_step. apply S_BinOp_Pop.
  eapply multi_step. 
    subcompute (eval_binop (ELeq, 2, 1)).
    apply S_If_Pop_Z.
  eapply multi_step. apply S_BinOp_Push.
  eapply multi_step. apply S_Call_Push.
  eapply multi_step. apply S_BinOp_Push.
  eapply multi_step. apply S_Read_Push.
  eapply multi_step. apply S_Read_Pop.
  eapply multi_step. 
    subcompute (fetch_state 1 0 0 (update_state 1 0 0 2 state_fact)).
    apply S_BinOp_Switch.
  eapply multi_step. apply S_BinOp_Pop.
  eapply multi_step.
    subcompute (eval_binop (EMinus, 2, 1)). 
    apply S_Call_Pop. reflexivity.
  eapply multi_step.
    subcompute ((fetch_state 1 0 0 state_fact)).
    subcompute (fetch_context 1 0 context_fact).
    apply S_If_Push.
  eapply multi_step. apply S_BinOp_Push. 
  eapply multi_step. apply S_Read_Push.
  eapply multi_step. apply S_Read_Pop.
  eapply multi_step.
    subcompute ((fetch_state 1 0 0 (update_state 1 0 0 1 (update_state 1 0 0 2 state_fact)))).
    apply S_BinOp_Switch.
  eapply multi_step. apply S_BinOp_Pop.
  eapply multi_step.
    subcompute (eval_binop (ELeq, 1, 1)).
  apply S_If_Pop_NZ. intro H. inversion H.
  eapply multi_step.
    subcompute ((fetch_state 1 0 0 (update_state 1 0 0 2 state_fact))).
    apply S_Return.
  eapply multi_step. apply S_BinOp_Switch.
  eapply multi_step. apply S_Read_Push.
  eapply multi_step. apply S_Read_Pop.
  eapply multi_step.
    subcompute ((fetch_state 1 0 0
       (update_state 1 0 0 2
          (update_state 1 0 0 1
             (update_state 1 0 0 2 state_fact))))).
    apply S_BinOp_Pop.
  eapply multi_step.
    subcompute (eval_binop (EMul, 1, 2)).
    apply S_Return.
  simpl. apply multi_refl.
Qed.   


(* _____________________________________ 
                PROOFS
   _____________________________________ *)

(* ---- Computational/Relational evaluation equivalence ---- *)

Lemma eval_cfg_1step: 
  forall (D:context) (c : cfg),
  (final_cfg c \/ D ⊢ c ⇒ eval_cfg D c 1).
Proof.
  intros.
  destruct c as [[[[C s] d] K] e].
  destruct e;
  destruct d as [|call d'];
  destruct K as [|k K'];
  try (left; constructor);
  try (destruct k);
  try (destruct call);
  try (destruct n);
  try (right; constructor);
  try (intro contra; inversion contra);
  try reflexivity.
Qed.

Lemma final_becomes_final :
  forall D n c,
  final_cfg c -> (eval_cfg D c n = c).  
Proof.
  intros.
  inversion H.
  Case "value".
    induction n as [|n']; simpl; reflexivity.
  Case "exit".
    induction n as [|n'].
    SCase "n = 0".
      simpl. reflexivity.
    SCase "n = S n'".
      destruct d; destruct K; reflexivity.
Qed.

Lemma eval_cfg_Sn_steps : 
  forall D c n,
  eval_cfg D (eval_cfg D c 1) n = eval_cfg D c (S n).
Proof.
  intros.
  pose (eval_cfg_1step D c) as lemma_1step.
  destruct lemma_1step.
  Case "final_cfg".
  { inversion H.
    SCase "final_value".
      induction n as [|n']; simpl; reflexivity.
    SCase "final_exit".
      induction n as [|n'].
      SSCase "n = 0".
        simpl; reflexivity.
      SSCase "n = S n'".
        destruct d;
        destruct K;
        repeat (simpl; reflexivity).
  }
  Case "non-final".
  { induction c as [[[[C s] d] K] e].
    destruct e;
    destruct d; destruct K; 
    try (destruct f); try (destruct c as [C' i' K']);
    try (apply final_becomes_final; try (apply final_value);
    try (destruct d; destruct K; constructor));
    try (simpl; reflexivity);
    try (constructor).
  }
Qed.

Theorem evalcfg_implies_smallstep :
  forall (i: nat) (D:context) (c : cfg),
  (D ⊢ c ⇒* (eval_cfg D c i)).
Proof.
  intros i D.
  induction i as [| i'].
  Case "i = 0".  
    { intros c. simpl. apply multi_refl. } 
  Case "i = S i'". 
    { intros c.
      rewrite <- (eval_cfg_Sn_steps D c i').
      pose (eval_cfg_1step D c) as lemma.
      destruct lemma.
      inversion H;
      SCase "final cfg";
        try (
          simpl; rewrite final_becomes_final;
          try (apply multi_refl); apply final_value
        );
        destruct d;
        [destruct K| ];
        simpl; rewrite final_becomes_final;
        try (apply multi_refl); apply final_exit.
      SCase "evaluable".
        eapply multi_step.
        apply H.
        apply IHi'.
    }
Qed.

Lemma smallstep_eval_1step :
  forall (D:context) (c c' : cfg),
  (D ⊢ c ⇒ c') -> eval_cfg D c 1 = c'.
Proof.
  intros D c c' H.
  destruct H;
  try destruct d;
  try destruct K;
  try destruct f;
  try destruct c;
  try destruct i;
  try reflexivity;
  try (now contradiction H);
  try (
    unfold eval_cfg;
    unfold basic_eval_cfg;
    rewrite H; reflexivity
  ).
Qed.

Theorem smallstep_implies_evalcfg :
  forall (D:context) (c c' : cfg),
  (D ⊢ c ⇒* c') -> (exists i, eval_cfg D c i = c').
Proof.
  intros.
  induction H.
  Case "multi_refl".
  { exists 0. reflexivity. }
  Case "multi_step".
  { destruct IHmulti.
    apply smallstep_eval_1step in H.
    exists (1+x0).
    rewrite <- eval_cfg_Sn_steps.
    rewrite H. apply H1.
  }
Qed.

Theorem smallstep_evalcfg_equivalence :
  forall (D:context) (c c' : cfg),
  (exists i, eval_cfg D c i = c') <-> (D ⊢ c ⇒* c'). 
Proof.
  intros. split.
  Case "->".
  { intro H; inversion H; clear H.
    rewrite <- H0. apply evalcfg_implies_smallstep.
  }
  Case "<-".
  { apply smallstep_implies_evalcfg. }
Qed.

(* ---- Determinism of evaluations ---- *)

Theorem smallstep_deterministic :
  forall (D:context) (c a b : cfg),
  (D ⊢ c ⇒ a) -> (D ⊢ c ⇒ b) -> a = b.
Proof.
  intros D c a b H0 H1.
  pose (smallstep_eval_1step D c a H0) as H0'.
  pose (smallstep_eval_1step D c b H1) as H1'.
  rewrite <- H0'. rewrite <- H1'. reflexivity.
Qed.








