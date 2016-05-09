Require Export Source.

(* _____________________________________ 
                  SYNTAX  
   _____________________________________ *)

Definition address : Type := nat.

(* For each component we have several procedures corresponding
to an entry point address *)
Definition entry_point : Type := address.
Definition entry_points : Type := list (list entry_point).

Definition fetch_entry_points 
  (C:component_id) (P:procedure_id) (E:entry_points)
  : entry_point :=
  nth P (nth C E []) 0.

Inductive binop : Type :=
  | Add
  | Minus
  | Mul.

Inductive instr : Type :=
  | Nop : instr
  | Const : nat -> address -> instr
  | Mov : address -> address -> instr
  | BinOp : binop -> address -> address -> address -> instr
  | Load : address -> address -> instr
  | Store : address -> address -> instr
  | Jal : address -> instr
  | Jump : address -> instr
  | Call : component_id -> procedure_id -> instr
  | Return : instr
  | Bnz : address -> nat -> instr
  | Halt : instr.

Definition eval_binop (e : binop * nat * nat) : nat :=
  match e with
  | (Add, a, b) => a+b
  | (Minus, a, b) => a-b
  | (Mul, a, b) => a*b
  end.

Definition register : Type := nat.
Definition registers : Type := list register. 

(* Each component has it's own memory *)
Definition memory : Type := list nat. 
Definition global_memory : Type := list memory.

Definition fetch_mem (C:component_id) (mem:global_memory) 
  (a:address) : nat := 
  nth C (nth a (mem) []) 0.

Definition decode (n:nat) : option instr := admit.

Definition encode (i:instr) : nat := admit.

Theorem decode_encode :
  forall (i:instr), decode (encode i) = Some i.
Admitted.

Definition procedure : Type :=
  list instr.

(* _____________________________________ 
                SEMANTICS
   _____________________________________ *)

Inductive protected_call : Type := 
  | PCall : component_id -> address -> protected_call.

Definition protected_callstack : Type := 
  list protected_call.

Definition state : Type := 
  (component_id * 
   protected_callstack * 
   global_memory * 
   registers * 
   address).

Definition fetch_reg (a:address) (reg:registers) : register :=
  nth a reg 0.

Definition update_reg (a:address) (i:nat)
  (reg:registers) : registers :=
  update_value a i reg.

Fixpoint update_mem (C:component_id) (mem:global_memory)
  (a:address) (new:nat) : global_memory :=
  match mem with
  | [] => []
  | h::t => match a with
            | 0 => (update_value a new h) :: t
            | S a' => h::(update_mem C mem a' new)
            end
  end.

Reserved Notation "I ;; E |- s '⇒' s'" (at level 40).
Inductive step (I:program_interfaces) (E:entry_points) : 
  state -> state -> Prop :=
  (* S_Nop *)
  | S_Nop : forall mem C pc i d reg, 
    (fetch_mem C mem pc = i) -> 
    (decode i = Some Nop) -> 
    I;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,pc+1)
  (* S_Const *)
  | S_Const : forall mem C pc i r i' d reg reg',
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Const i' r)) ->
    (update_reg r i' reg = reg') ->
    I;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_Mov *)
  | S_Mov : forall mem C pc i r1 r2 reg reg' d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Mov r1 r2)) ->
    (update_reg r2 (fetch_reg r1 reg) reg = reg') ->
    I;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_BinOp *)
  | S_BinOp : forall mem C pc i r1 r2 r3 reg reg' d op,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (BinOp op r1 r2 r3)) ->
    (update_reg r3 (eval_binop (op, (fetch_reg r1 reg), (fetch_reg r2 reg))) reg = reg') ->
    I;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_Load *)
  | S_Load : forall mem C pc i r1 r2 reg reg' d i1,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Load r1 r2)) ->
    (fetch_reg r1 reg = i1) ->
    (update_reg r2 (fetch_mem C mem i1) reg = reg') ->
    I;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_Store *)
  | S_Store : forall mem C pc i r1 r2 reg d i1 i2 mem',
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Store r1 r2)) ->
    (fetch_reg r1 reg = i1) ->
    (fetch_reg r2 reg = i2) ->
    (update_mem C mem i1 i2 = mem') ->
    I;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem',reg,pc+1)
  (* S_Jal *)
  | S_Jal : forall mem C pc i i' r reg reg' d rra,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Jal r)) ->
    (fetch_reg r reg = i') ->
    (update_reg rra (pc+1) reg = reg') ->
    I;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',i')
  (* S_Call *)
  | S_Call : forall mem C pc i reg d d' C' P',
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Call C' P')) ->
    (In (C',P') (get_import (nth C I (0,0,[]))) \/ C' = C) ->
    (d' = (PCall C (pc+1))::d) ->
    I;;E |- (C,d,mem,reg,pc) ⇒ (C',d',mem,reg,fetch_entry_points C' P' E)
  (* S_Jump *)
  | S_Jump : forall mem C pc i i' r reg d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Jump r)) ->
    (fetch_reg r reg = i') ->
    I;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,i')
  (* S_Return *)
  | S_Return : forall mem C pc i i' d' reg d C',
    (fetch_mem C mem pc = i) ->
    (decode i = Some Return) ->
    (d' = (PCall C' i')::d) ->
    I;;E |- (C,d,mem,reg,pc) ⇒ (C',d',mem,reg,i')
  (* S_BnzNZ *)
  | S_BnzNZ : forall mem C pc i i' r reg d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Bnz r i')) ->
    ~(fetch_reg r reg = 0) ->
    I;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,pc+1)
  (* S_BnzZ *)
  | S_BnzZ : forall mem C pc i i' r reg d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Bnz r i')) ->
    (fetch_reg r reg = 0) ->
    I;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,pc+1)
  where "I ;; E |- s '⇒' s'" := (step I E s s').

  
