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

(* ------- Definitions : small-step semantic definition ------- *)

Reserved Notation "D ⊢ e '⇒' e'" (at level 40).
Inductive smallStep : context -> cfg -> cfg -> Prop :=
  | S_BinOp_Push : forall D C s d K e1 e2 op,
    D ⊢ (C, s, d, K, EBinop op e1 e2) ⇒
    (C, s, d, (CHoleOp op e2)::K, e1)
  | S_BinOp_Switch : forall D C s d e2 K i1 op,
    D ⊢ (C, s, d, (CHoleOp op e2)::K, EVal i1) ⇒
    (C, s, d, (COpHole i1 op)::K, e2)
  | S_BinOp_Pop : forall D C s d i1 op K i2,
    D ⊢ (C, s, d, (COpHole i1 op)::K, EVal i2) ⇒
    (C, s, d, K, eval_binop (op, i1, i2))
  | S_If_Push : forall D C s d K e e1 e2,
    D ⊢ (C, s, d, K, (IFB e THEN e1 ELSE e2)) ⇒
    (C, s, d, (IFB □ THEN e1 ELSE e2)::K, e)
  | S_If_Pop_NZ : forall D C s d K e1 e2 i,
    ~(i=0) -> D ⊢ (C, s, d, (IFB □ THEN e1 ELSE e2)::K, EVal i) ⇒
    (C, s, d, K, e1)
  | S_If_Pop_Z : forall D C s d e1 e2 K,
    D ⊢ (C, s, d, (IFB □ THEN e1 ELSE e2)::K, EVal 0) ⇒
    (C, s, d, K, e2)
  | S_Read_Push : forall D C s d K b e,
    D ⊢ (C, s, d, K, ELoad b e) ⇒
    (C, s, d, (CHoleLoad b)::K, e)
  | S_Read_Pop : forall D C s d b K i,
    D ⊢ (C, s, d, (CHoleLoad b)::K, EVal i) ⇒
    (C, s, d, K, EVal (fetch_state C b i s))
  | S_Write_Push : forall D C s d K b e1 e2,
    D ⊢ (C, s, d, K, EStore b e1 e2) ⇒
    (C, s, d, (CHoleStore b e2)::K, e1)
  | S_Write_Swap : forall D C s d b e2 K i,
    D ⊢ (C, s, d, (CHoleStore b e2)::K, EVal i) ⇒
    (C, s, d, (CStoreHole b i)::K, e2)
  | S_Write_Pop : forall D C s d b i K i',
    D ⊢ (C, s, d, (CStoreHole b i)::K, EVal i') ⇒
    (C, (update_state C b i i' s), d, K, EVal i')
  | S_Call_Push : forall D C s d K C' P' e,
    D ⊢ (C, s, d, K, ECall C' P' e) ⇒
    (C, s, d, (CCallHole C' P')::K, e)
  | S_Call_Pop : forall D C' P' ep C s d K ia,
    (fetch_context C' P' D) = ep ->     
    D ⊢ (C, s, d, (CCallHole C' P')::K, EVal ia) ⇒
    (C', (update_state C' 0 0 ia s), (Call C (fetch_state C 0 0 s) K)::d, [], ep)
  | S_Return : forall D C s C' ia K d i,
    D ⊢ (C, s, (Call C' ia K)::d, [], i) ⇒
    (C', (update_state C 0 0 ia s), d, K, i)
  where "D ⊢ e '⇒' e'" := (smallStep D e e').

(* _____________________________________ 
                EXAMPLES
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
        IFB (LOAD 0<<EVal 0>>) THEN
          EVal 1
        ELSE
          EBinop EMul (CALL 0:::1 WITH EVal 2) (LOAD 0<<EVal 0>>)
      );
      (exit)
    ];

    (* C2 *)
    [
      (exit);
      (exit)
    ]
  ].

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
  IFB (LOAD 0<<EVal 0>>) THEN
    EVal 1
  ELSE
    EBinop EMul 
      (CALL 1:::0 WITH (EBinop EMinus LOAD 0<<EVal 0>> (EVal 1))) 
      (LOAD 0<<EVal 0>>).

Definition factorial_2 : expr :=
  CALL 1:::0 WITH EVal 2.

Example fact_2_eval :
  context_fact ⊢ (1, state_fact, [], [], factorial_2) ⇒ 
  (1, (update_state 0 0 0 2 state_fact), [], [], EVal 2).
Proof.
  unfold factorial_2. unfold state_fact.
  (* TODO *)
Admitted.   













