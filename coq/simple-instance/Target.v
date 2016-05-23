Require Export Source.

(* _____________________________________ 
                  SYNTAX  
   _____________________________________ *)

Definition address : Type := nat.

(* For each component we have several procedures corresponding
to an entry point address *)
Definition entry_point : Type := address.
Definition entry_points : Type := list (list entry_point).

Definition dom_entry_points (E:entry_points) : list component_id :=
  generate_intlist 0 (length E).    

Definition fetch_entry_points 
  (C:component_id) (P:procedure_id) (E:entry_points)
  : entry_point :=
  nth P (nth C E []) 0.

Definition register : Type := nat.

Definition nb_regs : nat := 7.
Definition r_pc : register :=
  0.
Definition r_one : register :=
  1.
Definition r_com : register :=
  2.
Definition r_aux1 : register :=
  3.
Definition r_aux2 : register :=
  4.
Definition r_ra : register :=
  5.
Definition r_sp : register :=
  6.

Definition registers : Type := list register.

Inductive LLbinop : Set :=
  | Add :  LLbinop
  | Minus : LLbinop
  | Mul : LLbinop
  | Eq : LLbinop
  | Leq : LLbinop.

Inductive instr : Type :=
  | Nop : instr
  | Const : nat -> address -> instr
  | Mov : address -> address -> instr
  | BinOp : LLbinop -> address -> address -> address -> instr
  | Load : address -> address -> instr
  | Store : address -> address -> instr
  | Jal : address -> instr
  | Jump : address -> instr
  | Call : component_id -> procedure_id -> instr
  | Return : instr
  | Bnz : address -> nat -> instr
  | Halt : instr.

Definition LLeval_binop (e : LLbinop * nat * nat) : nat :=
  match e with
  | (Add, a, b) => a+b
  | (Minus, a, b) => a-b
  | (Mul, a, b) => a*b
  | (Eq, a, b) => if beq_nat a b then 1 else 0
  | (Leq, a, b) => if ble_nat a b then 1 else 0 
  end.

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

Inductive protected_call : Type := 
  | PCall : component_id -> address -> protected_call.

Definition protected_callstack : Type := 
  list protected_call.

Definition code : Type :=
  list instr.

Definition component_memory : Type :=
  (code * protected_callstack * buffer).

Definition program : Type :=
  (program_interfaces * memory * entry_points).

(* _____________________________________ 
                SEMANTICS
   _____________________________________ *)

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

Definition call_exists (Is:program_interfaces)
  (C:component_id) (P:procedure_id) : Prop :=
  let l := length Is in
  let import := get_import (nth C Is (0,0,[])) in
  (ble_nat C l) && negb (beq_nat C l) = true /\ (In (C,P) import).

Definition boolean_call_exists (Is:program_interfaces)
  (C:component_id) (P:procedure_id) : bool :=
  let l := length Is in
  let import := get_import (nth C Is (0,0,[])) in
  (ble_nat C l) && negb (beq_nat C l) 
    &&
  (existsb (fun x => (fst x =? C) && (snd x =? P)) import).

Reserved Notation "Is ;; E |- s '⇒' s'" (at level 40).
Inductive step (Is:program_interfaces) (E:entry_points) : 
  state -> state -> Prop :=
  (* S_Nop *)
  | S_Nop : forall mem C pc i d reg, 
    (fetch_mem C mem pc = i) -> 
    (decode i = Some Nop) -> 
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,pc+1)
  (* S_Const *)
  | S_Const : forall mem C pc i r i' d reg reg',
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Const i' r)) ->
    (update_reg r i' reg = reg') ->
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_Mov *)
  | S_Mov : forall mem C pc i r1 r2 reg reg' d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Mov r1 r2)) ->
    (update_reg r2 (fetch_reg r1 reg) reg = reg') ->
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_BinOp *)
  | S_BinOp : forall mem C pc i r1 r2 r3 reg reg' d op,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (BinOp op r1 r2 r3)) ->
    (update_reg r3 (LLeval_binop (op, (fetch_reg r1 reg), (fetch_reg r2 reg))) reg = reg') ->
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_Load *)
  | S_Load : forall mem C pc i r1 r2 reg reg' d i1,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Load r1 r2)) ->
    (fetch_reg r1 reg = i1) ->
    (update_reg r2 (fetch_mem C mem i1) reg = reg') ->
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_Store *)
  | S_Store : forall mem C pc i r1 r2 reg d i1 i2 mem',
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Store r1 r2)) ->
    (fetch_reg r1 reg = i1) ->
    (fetch_reg r2 reg = i2) ->
    (update_mem C mem i1 i2 = mem') ->
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem',reg,pc+1)
  (* S_Jal *)
  | S_Jal : forall mem C pc i i' r reg reg' d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Jal r)) ->
    (fetch_reg r reg = i') ->
    (update_reg r_ra (pc+1) reg = reg') ->
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',i')
  (* S_Call *)
  | S_Call : forall mem C pc i reg d d' C' P',
    (fetch_mem C mem pc = i) ->
    call_exists Is C' P' ->
    (decode i = Some (Call C' P')) ->
    (In (C',P') (get_import (nth C Is (0,0,[]))) \/ C' = C) ->
    (d' = (PCall C (pc+1))::d) ->
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C',d',mem,reg,fetch_entry_points C' P' E)
  (* S_Jump *)
  | S_Jump : forall mem C pc i i' r reg d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Jump r)) ->
    (fetch_reg r reg = i') ->
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,i')
  (* S_Return *)
  | S_Return : forall mem C pc i i' d' reg d C',
    (fetch_mem C mem pc = i) ->
    (decode i = Some Return) ->
    (d = (PCall C' i')::d') ->
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C',d',mem,reg,i')
  (* S_BnzNZ *)
  | S_BnzNZ : forall mem C pc i i' r reg d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Bnz r i')) ->
    ~(fetch_reg r reg = 0) ->
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,pc+i')
  (* S_BnzZ *)
  | S_BnzZ : forall mem C pc i i' r reg d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Bnz r i')) ->
    (fetch_reg r reg = 0) ->
    Is;;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,pc+1)
  where "Is ;; E |- s '⇒' s'" := (step Is E s s').

Inductive stuck_state : program_interfaces -> state -> Prop :=
  (* S_DecodingError *)
  | S_DecodingError : forall Is i C d mem reg pc,
    (fetch_mem C mem pc = i) ->
    (decode i = None) -> stuck_state Is (C,d,mem,reg,pc)
  (* S_CallFail *)
  | S_CallFail : forall Is i C C' P' d mem reg pc,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Call C' P')) ->
    ~(call_exists Is C' P') ->
    stuck_state Is (C,d,mem,reg,pc)
  (* S_EmptyCallStack *)
  | S_EmptyCallStack : forall Is C mem reg pc,
    stuck_state Is (C,[],mem,reg,pc)
  (* S_Halt *)
  | S_Halt : forall Is i C d mem reg pc,
    (fetch_mem C mem pc = i) ->
    (decode i = Some Halt) ->
    stuck_state Is (C,d,mem,reg,pc).

Definition boolean_stuckstate (Is:program_interfaces) 
  (cfg:state) : bool :=
  match cfg with
  (* S_EmptyCallStack *)
  | (C,[],mem,reg,pc) => true
  | (C,d,mem,reg,pc) =>
    let i := fetch_mem C mem pc in
    match (decode i) with
    (* S_CallFail *)
    | Some (Call C' P') =>
      if (boolean_call_exists Is C' P') then
        false
      else
        true
    (* S_Halt *)
    | Some Halt => true 
    (* S_DecodingError & Non-stuck states *)
    | _ => false
    end   
  end.

(* _____________________________________ 
          EVALUATION FUNCTION
   _____________________________________ *)

Definition basic_eval_step (Is:program_interfaces) (E:entry_points) 
  (cfg:state) : state :=
  match cfg with
  | (C,d,mem,reg,pc) =>
    let i := fetch_mem C mem pc in
    match (decode i) with
    (* S_Nop *)
    | Some Nop =>
      (C,d,mem,reg,pc+1)
    (* S_Const *)
    | Some (Const i' r) => 
      let reg' := (update_reg r i' reg) in
      (C,d,mem,reg',pc+1)
    (* S_Mov *)
    | Some (Mov r1 r2) =>
      let reg' := (update_reg r2 (fetch_reg r1 reg) reg) in
      (C,d,mem,reg',pc+1)
    (* S_BinOp *)
    | Some (BinOp op r1 r2 r3) =>
      let reg' := (update_reg r3 (LLeval_binop 
        (op, (fetch_reg r1 reg), (fetch_reg r2 reg))) reg) in
      (C,d,mem,reg',pc+1)
    (* S_Load *)
    | Some (Load r1 r2) =>
      let i1 := (fetch_reg r1 reg) in
      let reg' := (update_reg r2 (fetch_mem C mem i1) reg) in
      (C,d,mem,reg',pc+1)
    (* S_Store *)
    | Some (Store r1 r2) =>
      let i1 := (fetch_reg r1 reg) in
      let i2 := (fetch_reg r2 reg) in
      let mem' := (update_mem C mem i1 i2) in
      (C,d,mem',reg,pc+1)
    (* S_Jal *)
    | Some (Jal r) =>
      let i' := (fetch_reg r reg) in
      let reg' := (update_reg r_ra (pc+1) reg) in
      (C,d,mem,reg',i')
    (* S_Call *)
    | Some (Call C' P') =>
      if ((boolean_call_exists Is C' P') 
          && 
         (existsb (fun x => (fst x =? C') && (snd x =? P')) (get_import (nth C Is (0,0,[])))
            ||
        beq_nat C' C)) then
        let d' := (PCall C (pc+1))::d in 
        (C',d',mem,reg,fetch_entry_points C' P' E)
      else
        cfg
    (* S_Jump *)
    | Some (Jump r) =>
      let i' := (fetch_reg r reg) in
      (C,d,mem,reg,i')
    (* S_Return *)
    | Some Return =>
      match d with
      | [] => cfg
      | (PCall C' i')::d' => (C',d',mem,reg,i')
      end
    (* S_BnzNZ *)
    | Some (Bnz r i') =>
      if negb (fetch_reg r reg =? 0) then
        (C,d,mem,reg,pc+i')
      else
        (C,d,mem,reg,pc+1)
    | _ => cfg
    end
  end.

Fixpoint eval_step (Is:program_interfaces) (E:entry_points) 
  (cfg:state) (limit:nat) : state :=
  match limit with
  | 0 =>
    match cfg with
    | (C,d,mem,reg,pc) => (C,d,mem,reg,pc+1)
    end
  | S n => 
    match cfg with
    (* S_EmptyCallStack *)    
    | (C,[],mem,reg,pc) => (C,[],mem,reg,pc+1)
    | (C,d,mem,reg,pc) =>
      let i := fetch_mem C mem pc in
      match (decode i) with
      (* S_CallFail *)
      | Some (Call C' P') =>
        if (negb (boolean_call_exists Is C' P')) then
          (C,d,mem,reg,pc+1)
        else
          eval_step Is E (basic_eval_step Is E cfg) n
      (* S_Halt *)
      | Some Halt => (C,d,mem,reg,pc+1)
      (* S_DecodingError *)
      | None => (C,d,mem,reg,pc+1)
      (* Other cases *)
      | _ => eval_step Is E (basic_eval_step Is E cfg) n
      end
    end
  end.

(* _____________________________________ 
          PROOF : DETERMINISM
   _____________________________________ *)

Lemma step_eval_1step :
  forall Is E cfg1 cfg2,
  (Is;;E |- cfg1 ⇒ cfg2) -> eval_step Is E cfg1 1 = cfg2.
Proof.
Admitted.

Theorem abstractmachine_determinism :
  forall Is E cfg cfg1 cfg2,
  (Is;;E |- cfg ⇒ cfg1) /\ (Is;;E |- cfg ⇒ cfg2) ->
  cfg1 = cfg2.
Proof.
  intros. destruct H as [Hcfg1 Hcfg2].
  apply step_eval_1step in Hcfg1.
  apply step_eval_1step in Hcfg2.
  rewrite <- Hcfg1. rewrite <- Hcfg2.
  reflexivity.
Qed.


