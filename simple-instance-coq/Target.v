Require Import Source.

(* _____________________________________ 
                  SYNTAX  
   _____________________________________ *)

Definition address : Type := nat.

(* For each component we have several procedures corresponding
to an entry point address *)
Definition entry_point : Type := address.
Definition entry_points : Type := 
  list (option (list entry_point)).

Definition dom_entry_points (E:entry_points) : 
  list (option component_id) :=
  let indices := seq 0 (length E) in
  let combination := combine E indices in
  let f p := 
    match p with
    | (val,i) =>
      match val with
      | Some _ => [Some i]
      | None => [None]
      end
    end
  in
  concat (map f combination).

Definition fetch_entry_points 
  (C:component_id) (P:procedure_id) (E:entry_points)
  : entry_point :=
  match (nth C E None) with
  | Some E' => nth P E' 0 
  | None => 0
  end.

(* ------- Begin Definitions : Registers ------- *)

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
Definition g_regs : registers :=
  map (fun x => 0) (seq 0 nb_regs).

(* ------- End Definitions : Registers ------- *)

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
Definition global_memory : Type := list (option memory).

Definition dom_global_memory (mem:global_memory) :
  list (option component_id) :=
  let indices := seq 0 (length mem) in
  let combination := combine mem indices in
  let f p := 
    match p with
    | (val,i) =>
      match val with
      | Some _ => [Some i]
      | None => [None]
      end
    end
  in
  concat (map f combination).

Definition fetch_mem (C:component_id) (mem:global_memory) 
  (a:address) : option nat := 
  match (nth a mem None) with
  | Some l => Some (nth C l 0)
  | _ => None
  end.

Definition code : Type :=
  list instr.

Definition decode (n:option nat) : option instr := admit.

Definition encode (i:instr) : option nat := admit.

Definition encode_code (c:code) : list nat := admit.

Theorem decode_encode :
  forall (i:instr), decode (encode i) = Some i.
Admitted.

Inductive protected_call : Type := 
  | PCall : component_id -> address -> protected_call.

Definition protected_callstack : Type := 
  list protected_call.

Definition component_memory : Type :=
  (code * protected_callstack * buffer).

Definition program : Type :=
  (partial_program_interfaces * global_memory * entry_points).

Definition get_interfacesLLP (P:program) :=
  match P with
  | (Is, _, _) => Is
  end.

Definition get_memLLP (P:program) :=
  match P with
  | (_, mem, _) => mem
  end.

Definition get_entrypointsLLP (P:program) :=
  match P with
  | (_, _, E) => E
  end.

(* _____________________________________ 
                SEMANTICS
   _____________________________________ *)

Definition state : Type := 
  (component_id * 
   protected_callstack * 
   global_memory * 
   registers * 
   address).

(* ------- Definitions : useful functions ------- *)
Definition fetch_reg (a:address) (reg:registers) : register :=
  nth a reg 0.

Fixpoint update_reg_value (a : address) (i' : option nat)
  (reg : registers) : memory :=
  match reg with
  | [] => []
  | h :: t =>
      match a with
      | 0 => 
        match i' with
        | Some v => v :: t
        | None => 0 :: t
        end
      | S n => h :: update_reg_value n i' t
      end
  end.

Definition update_reg (a:address) (i:option nat)
  (reg:registers) : registers :=
  update_reg_value a i reg.

Fixpoint clear_regs_aux (l:list nat) k (i:nat) :=
  match l with
    | [] => []
    | x :: l' =>
      let x' := if eq_nat_dec i k then x else 0 in
        x' :: (clear_regs_aux l' k (i+1))
  end.

Definition clear_regs l := clear_regs_aux l r_com 0.

Fixpoint update_mem (C:component_id) (mem:global_memory)
  (a:address) (new:nat) : global_memory :=
  match mem with
  | [] => []
  | h::t => 
    match C with
    | 0 => 
      match h with
      | Some h' => Some (update_value a new h') :: t
      | None => mem
      end
    | S C' => h::(update_mem C' mem a new)
    end
  end.

Definition call_exists (Is:partial_program_interfaces)
  (C:component_id) (P:procedure_id) : Prop :=
  match (nth C Is None) with
  | Some i =>
    let l := length Is in
    let import := get_import i in
    (ble_nat C l) && negb (beq_nat C l) = true /\ (In (C,P) import)
  | None => False
  end.

Definition boolean_call_exists (Is:partial_program_interfaces)
  (C:component_id) (P:procedure_id) : bool :=
  let l := length Is in
  match (nth C Is None) with
  | Some i =>
    let import := get_import i in
    (ble_nat C l) && negb (beq_nat C l) 
      &&
    (existsb (fun x => (fst x =? C) && (snd x =? P)) import)
  | None => false
  end.

(* ------- Definitions : operational semantics ------- *)
Reserved Notation "'LOW_LEVEL' Is ; E |- s '⇒' s'" (at level 40).
Inductive step (Is:partial_program_interfaces) (E:entry_points) : 
  state -> state -> Prop :=
  (* S_Nop *)
  | S_Nop : forall mem C pc i d reg, 
    (fetch_mem C mem pc = i) -> 
    (decode i = Some Nop) -> 
    LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,pc+1)
  (* S_Const *)
  | S_Const : forall mem C pc i r i' d reg reg',
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Const i' r)) ->
    (update_reg r (Some i') reg = reg') ->
    LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_Mov *)
  | S_Mov : forall mem C pc i r1 r2 reg reg' d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Mov r1 r2)) ->
    (update_reg r2 (Some (fetch_reg r1 reg)) reg = reg') ->
    LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_BinOp *)
  | S_BinOp : forall mem C pc i r1 r2 r3 reg reg' d op,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (BinOp op r1 r2 r3)) ->
    (update_reg r3 (Some (LLeval_binop (op, (fetch_reg r1 reg), (fetch_reg r2 reg)))) reg = reg') ->
    LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_Load *)
  | S_Load : forall mem C pc i r1 r2 reg reg' d i1,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Load r1 r2)) ->
    (fetch_reg r1 reg = i1) ->
    (update_reg r2 (fetch_mem C mem i1) reg = reg') ->
    LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',pc+1)
  (* S_Store *)
  | S_Store : forall mem C pc i r1 r2 reg d i1 i2 mem',
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Store r1 r2)) ->
    (fetch_reg r1 reg = i1) ->
    (fetch_reg r2 reg = i2) ->
    (update_mem C mem i1 i2 = mem') ->
    LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem',reg,pc+1)
  (* S_Jal *)
  | S_Jal : forall mem C pc i i' r reg reg' d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Jal r)) ->
    (fetch_reg r reg = i') ->
    (update_reg r_ra (Some (pc+1)) reg = reg') ->
    LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg',i')
  (* S_Call *)
  | S_Call : forall mem C pc i reg d d' C' P',
    (fetch_mem C mem pc = i) ->
    call_exists Is C' P' ->
    (decode i = Some (Call C' P')) ->
    match (nth C Is None) with
    | Some i =>
      (In (C',P') (get_import i) \/ C' = C)
    | None => False \/ C' = C
    end ->
      (d' = (PCall C (pc+1))::d) ->
      LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C',d',mem,reg,fetch_entry_points C' P' E)
  (* S_Jump *)
  | S_Jump : forall mem C pc i i' r reg d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Jump r)) ->
    (fetch_reg r reg = i') ->
    LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,i')
  (* S_Return *)
  | S_Return : forall mem C pc i i' d' reg d C',
    (fetch_mem C mem pc = i) ->
    (decode i = Some Return) ->
    (d = (PCall C' i')::d') ->
    LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C',d',mem,reg,i')
  (* S_BnzNZ *)
  | S_BnzNZ : forall mem C pc i i' r reg d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Bnz r i')) ->
    ~(fetch_reg r reg = 0) ->
    LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,pc+i')
  (* S_BnzZ *)
  | S_BnzZ : forall mem C pc i i' r reg d,
    (fetch_mem C mem pc = i) ->
    (decode i = Some (Bnz r i')) ->
    (fetch_reg r reg = 0) ->
    LOW_LEVEL Is;E |- (C,d,mem,reg,pc) ⇒ (C,d,mem,reg,pc+1)
  where "'LOW_LEVEL' Is ; E |- s '⇒' s'" := (step Is E s s').

(* ------- Definitions : Multi-step reduction ------- *)
Definition LV_multi_step 
  (Is:partial_program_interfaces) (E:entry_points)
  (e e':state) := 
    (multi (step Is E) e e').

(* ------- Definitions : Irreducibility ------- *)
Definition state_irreducible 
  (Is:partial_program_interfaces) (E:entry_points) 
  (cfg:state) : Prop :=
  ~(exists cfg', (step Is E cfg cfg')).

(* ------- Definitions : Special reduction state ------- *)
Definition LL_initial_cfg_of (P:program) : state :=
  match P with
  | (Is, mem, E) =>
    let ep :=
      match (nth main_cid E None) with
      | Some E' => nth 0 E' 0
      | None => 0
      end    
    in
    (main_cid, [], mem, g_regs, ep)
  end.

Inductive stuck_state : 
  partial_program_interfaces -> state -> Prop :=
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

Definition boolean_stuckstate (Is:partial_program_interfaces) 
  (cfg:state) : bool :=
  match cfg with
  | (C,d,mem,reg,pc) =>
    let i := fetch_mem C mem pc in
    match (decode i) with
    (* S_Return_EmptyCallStack *)
    | Some Return => 
      if (length d =? 0) then
        true
      else
        false
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

Definition basic_eval_step 
  (Is:partial_program_interfaces) (E:entry_points) 
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
      let reg' := (update_reg r (Some i') reg) in
      (C,d,mem,reg',pc+1)
    (* S_Mov *)
    | Some (Mov r1 r2) =>
      let reg' := (update_reg r2 (Some (fetch_reg r1 reg)) reg) in
      (C,d,mem,reg',pc+1)
    (* S_BinOp *)
    | Some (BinOp op r1 r2 r3) =>
      let reg' := (update_reg r3 (Some (LLeval_binop 
        (op, (fetch_reg r1 reg), (fetch_reg r2 reg)))) reg) in
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
      let reg' := (update_reg r_ra (Some (pc+1)) reg) in
      (C,d,mem,reg',i')
    (* S_Call *)
    | Some (Call C' P') =>
      let imp := 
        match (nth C Is None) with
        | Some i => (get_import i)
        | None => []
        end
      in
      if ((boolean_call_exists Is C' P') 
          && 
         (existsb (fun x => (fst x =? C') && (snd x =? P')) imp)
            ||
        beq_nat C' C) then
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

Fixpoint eval_step 
  (Is:partial_program_interfaces) (E:entry_points) 
  (cfg:state) (limit:nat) : state :=
  match limit with
  | 0 => cfg
  | S n => 
    match cfg with
    | (C,d,mem,reg,pc) =>
      if boolean_stuckstate Is cfg then
        cfg
      else
        eval_step Is E (basic_eval_step Is E cfg) n
    end
  end.

(* _____________________________________ 
          PROOF : DETERMINISM
   _____________________________________ *)

Lemma in_import_eq :
  forall C' P' i,
  In (C', P') (get_import i) ->
  existsb (fun x : nat * nat =>
    (fst x =? C') && (snd x =? P')) (get_import i) = true.
Proof.
  intros.
  induction (get_import i).
  - inversion H.
  - simpl in H. destruct H.
    + rewrite H. simpl.
      assert ((C' =? C') && (P' =? P') = true) as Ha.
      rewrite <- (beq_nat_refl C').
      rewrite <- (beq_nat_refl P').
      trivial. rewrite Ha. simpl. trivial.
    + apply IHl in H. simpl. rewrite H.
      apply orb_comm.
Qed.

Lemma callexists_boolean_eq :
  forall Is C' P',
  call_exists Is C' P' -> boolean_call_exists Is C' P' = true.
Proof.
  intros. unfold call_exists in H. unfold boolean_call_exists.
  destruct (nth C' Is None).
  - destruct H. rewrite H. apply in_import_eq in H0.
    rewrite H0. trivial.
  - contradiction.
Qed.

Lemma step_eval_1step :
  forall Is E cfg1 cfg2,
  (LOW_LEVEL Is;E |- cfg1 ⇒ cfg2) -> eval_step Is E cfg1 1 = cfg2.
Proof.
  intros.
  destruct cfg1 as [[[[C1 d1] mem1] reg1] pc1].
  destruct cfg2 as [[[[C2 d2] mem2] reg2] pc2].
  induction H;
  rename H into H_fetch; rename H0 into H_decode;
  unfold eval_step; unfold boolean_stuckstate;
  rewrite H_fetch; try (rewrite H_decode); simpl;
  rewrite H_fetch; try (rewrite H_decode); simpl;
  try (subst; reflexivity).
  - rewrite H1. simpl.
    destruct (boolean_call_exists Is C' P') eqn:HD.
    + simpl. destruct (nth C Is None). destruct H2; rewrite H3.
      apply in_import_eq in H. rewrite H. simpl. reflexivity.
      rewrite H. assert (C =? C = true).
      { symmetry. apply beq_nat_refl. }
      rewrite H0. remember (existsb (fun x : nat * nat =>
      (fst x =? C) && (snd x =? P')) (get_import i0)) as t_exists.
      rewrite (orb_comm t_exists true). simpl. reflexivity.
      destruct H2. contradiction.
      rewrite H. assert (C =? C = true).
      { symmetry. apply beq_nat_refl. }
      rewrite H0. simpl. rewrite H3. reflexivity.
    + destruct (nth C Is None).
      * destruct H2; apply callexists_boolean_eq in H_decode;
        rewrite H_decode in HD; inversion HD.
      * destruct H2; apply callexists_boolean_eq in H_decode;
        rewrite H_decode in HD; inversion HD.
  - apply false_beq_nat in H1. rewrite H1. simpl. reflexivity.
  - rewrite H1. simpl. reflexivity.
Qed.

Theorem abstractmachine_determinism :
  forall Is E cfg cfg1 cfg2,
  (LOW_LEVEL Is;E |- cfg ⇒ cfg1) /\ (LOW_LEVEL Is;E |- cfg ⇒ cfg2) ->
  cfg1 = cfg2.
Proof.
  intros. destruct H as [Hcfg1 Hcfg2].
  apply step_eval_1step in Hcfg1.
  apply step_eval_1step in Hcfg2.
  rewrite <- Hcfg1. rewrite <- Hcfg2.
  reflexivity.
Qed.


