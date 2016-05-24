Require Export Source.
Require Export Target.

(* _____________________________________ 
        COMPARTMENT MEMORY LAYOUT
   _____________________________________ *)

Fixpoint BUFADDR (k:component) (b:buffer_id) : address :=
  match b with
  | 0 => 0
  | S b' =>
    let bnum := (get_bnum k) in
    let l := length (nth b' (get_buffers k) []) in 
    if ble_nat b' bnum then
      (BUFADDR k b') + l
    else
      0
  end.

Fixpoint compiled_length (k:component) (e:expr) : nat :=
  match e with
  | EVal _ => 1
  | EBinop ESeq e1 e2 => (compiled_length k e1) + (compiled_length k e2)
  | EBinop _ e1 e2 => (compiled_length k e1) + (compiled_length k e2) + 5
  | EIfThenElse e e1 e2 => 
    (compiled_length k e) + (compiled_length k e1) + (compiled_length k e2) + 3
  | ELoad _ e => (compiled_length k e) + 3
  | EStore _ e1 e2 => (compiled_length k e1) + (compiled_length k e2) + 7
  | ECall C' P' e=> 
    if (negb (C' =? (get_nameC k))) then 
      (compiled_length k e) + nb_regs + 17
    else
      (compiled_length k e) + 14
  | EExit => 1
  end.

Fixpoint EXTERNALENTRY (k:component) (P:procedure_id) :
  address :=
  match P with
  | 0 => 
    let bnum := (get_bnum k) in
    let l := length (nth (pred bnum) (get_buffers k) []) in 
    (BUFADDR k (pred bnum)) + l
  | S P' => 
    let length_expr := compiled_length k (nth P (get_procs k) EExit) in 
    if ble_nat P (get_pnum k) then 
      (EXTERNALENTRY k P') + length_expr
    else
      0
  end.

Definition INTERNALENTRY (k:component) (P:procedure_id) : 
  address := 
  (EXTERNALENTRY k P) + 3.

Definition STACKBASE (k:component) : address :=
  let length_expr := 
    compiled_length k (nth (pred (get_pnum k)) (get_procs k) EExit) in
  (EXTERNALENTRY k (pred (get_pnum k))) + length_expr + 1.

(* _____________________________________ 
                MACROS
   _____________________________________ *)

Definition list_regs : registers :=
  generate_intlist 0 nb_regs.

Definition CLEARREG : code :=
  map (fun r => Const 0 r) list_regs.

Definition STOREENV (k:component) (r:register) :=
  [Const (pred (STACKBASE k)) r;
   Store r r_sp].

Definition RESTOREENV (k:component) :=
  [Const 1 r_one;
   Const (pred (STACKBASE k)) r_sp;
   Load r_sp r_sp].

Definition LOADARG (k:component) (r:register) :=
  [Const (BUFADDR k 0) r; 
   Load r r].

Definition STOREARG (k:component) (r r':register) :=
  [Const (BUFADDR k 0) r';
   Store r' r].

Definition PUSH (r:register) :=
  [BinOp Add r_sp r_one r_sp;
  Store r_sp r].

Definition POP (r:register) :=
  [Load r_sp r;
   BinOp Minus r_sp r_one r_sp].

(* _____________________________________ 
          PROCEDURE COMPILATION
   _____________________________________ *)

Fixpoint compile_expr (k:component) (e:expr) : code :=
  match e with
  (* EVal *)
  | EVal i =>
    [Const i r_com]
  (* EBinop Seq *)
  | EBinop ESeq e1 e2 =>
    (compile_expr k e1) ++
    (compile_expr k e2)
  (* EBinop *)
  | EBinop EAdd e1 e2 =>
    (compile_expr k e1) ++
    (PUSH r_com) ++
    (compile_expr k e2) ++
    (POP r_aux1) ++
    [BinOp Add r_aux1 r_com r_com]
  | EBinop EMinus e1 e2 =>
    (compile_expr k e1) ++
    (PUSH r_com) ++
    (compile_expr k e2) ++
    (POP r_aux1) ++
    [BinOp Minus r_aux1 r_com r_com]
  | EBinop EMul e1 e2 =>
    (compile_expr k e1) ++
    (PUSH r_com) ++
    (compile_expr k e2) ++
    (POP r_aux1) ++
    [BinOp Mul r_aux1 r_com r_com]
  | EBinop EEq e1 e2 =>
    (compile_expr k e1) ++
    (PUSH r_com) ++
    (compile_expr k e2) ++
    (POP r_aux1) ++
    [BinOp Eq r_aux1 r_com r_com]
  | EBinop ELeq e1 e2 =>
    (compile_expr k e1) ++
    (PUSH r_com) ++
    (compile_expr k e2) ++
    (POP r_aux1) ++
    [BinOp Leq r_aux1 r_com r_com]
  (* EIfThenElse *)
  | EIfThenElse e e1 e2 =>
    let lnz := 3 in
    let lend := 2 in
    (compile_expr k e) ++
    [Bnz r_com lnz] ++
    (compile_expr k e2) ++
    [Bnz r_one lend] ++
    (compile_expr k e1) ++
    [Nop]
  (* ELoad *)
  | ELoad b e =>
    (compile_expr k e) ++
    [Const (BUFADDR k b) r_aux1] ++
    [BinOp Add r_aux1 r_com r_aux1] ++
    [Load r_aux1 r_com]
  (* EStore *)
  | EStore b e1 e2 =>
    (compile_expr k e1) ++
    [Const (BUFADDR k b) r_aux1] ++
    [BinOp Add r_aux1 r_com r_aux1] ++
    (PUSH r_aux1) ++
    (compile_expr k e2) ++
    (POP r_aux1) ++
    [Store r_aux1 r_com]
  (* Call *)
  | ECall C' P' e =>
    if (negb (C' =? (get_nameC k))) then
      (compile_expr k e) ++
      (PUSH r_aux2) ++
      (LOADARG k r_aux1) ++
      (PUSH r_aux1) ++
      (STOREENV k r_aux1) ++
      (CLEARREG) ++
      [Call C' P'] ++
      (RESTOREENV k) ++
      (POP r_aux1) ++
      (STOREARG k r_aux1 r_aux2) ++
      (POP r_aux2)
    else
      (compile_expr k e) ++
      (PUSH r_aux2) ++
      (LOADARG k r_aux1) ++
      (PUSH r_aux1) ++
      [Const (INTERNALENTRY k P') r_aux1] ++
      [Jal r_aux1] ++
      (POP r_aux1) ++
      (STOREARG k r_aux1 r_aux2) ++
      (POP r_aux2)
  | EExit => 
    [Halt]
  end.

Notation "'COMPILE_EXPR' ( k , e )↓ " := 
  (compile_expr k e) (at level 0).


(* _____________________________________ 
          PROCEDURE COMPILATION
   _____________________________________ *)

Definition compile_proc (k:component) (P:procedure_id) : code :=
  let lmain := 3 in
  let lret := 3 in
  (* lext *)  
  [Const 1 r_aux2] ++ 
  (RESTOREENV k) ++
  [Bnz r_one lmain] ++
  (* lint *)
  [Const 0 r_aux2] ++ 
  (PUSH r_ra) ++
  (* lmain *) 
  (STOREARG k r_com r_aux1) ++
  (compile_expr k (nth P (get_procs k) EExit)) ++
  [Bnz r_aux2 lret] ++
  (POP r_ra) ++
  [Jump r_ra] ++
  (* lret *)
  (STOREENV k r_aux1) ++
  (CLEARREG) ++
  [Return].

Notation "'COMPILE_PROC' ( k , P )↓ " := 
  (compile_proc k P) (at level 0).


(* _____________________________________ 
          COMPONENT COMPILATION
   _____________________________________ *)

Definition component_allocated_memory : nat := 1000.

Definition compile_component (k:Source.component) : Target.program :=
  let Is := [interfaceof_C k] in
  let mem := 
    [(concat (get_buffers k)) ++
    (concat (map encode_code 
      (map (compile_proc k) (generate_intlist 0 (get_pnum k))))) ++
    [STACKBASE k] ++
    (map (fun x => 0) (seq 0 component_allocated_memory))] in
  let E := [map (EXTERNALENTRY k) 
    (generate_intlist 0 (get_pnum k))] in
  (Is, mem, E).


(* _____________________________________ 
        PARTIAL PROGRAM COMPILATION
   _____________________________________ *)

Definition fusion_compiled_program
  (ck1:Target.program) (ck2:Target.program) : Target.program :=
  match ck1 with
  | (Is1, mem1, E1) =>
    match ck2 with
    | (Is2, mem2, E2) =>
      (Is1++Is2, mem1++mem2, E1++E2)
    end
  end.

Definition compile_partial_program (P:Source.program) : 
  Target.program :=
  let compiled_components := map compile_component P in
  fold_right fusion_compiled_program ([],[],[]) compiled_components.


(* _____________________________________ 
               PROPERTIES
   _____________________________________ *)

Definition program_terminates (P:Source.program) : Prop :=
  let D := procbodies P in
  exists cfg, D ⊢ (initial_cfg_of P) ⇒ cfg
    /\
  D ⊢ cfg ↛.

Definition program_diverges (P:Source.program) : Prop :=
  let D := procbodies P in
  forall cfg, (D ⊢ (initial_cfg_of P) ⇒* cfg) ->
    exists cfg', D ⊢ cfg ⇒ cfg'.

Definition cprogram_terminates (P:Target.program) : Prop :=
  match P with
  | (Is, mem, E) =>
    exists cfg, (step Is E (LL_initial_cfg_of P) cfg)
      /\
    (state_irreducible Is E cfg) 
  end.

Definition cprogram_diverges (P:Target.program) : Prop :=
  match P with
  | (Is, mem, E) =>
    forall cfg, (LV_multi_step Is E (LL_initial_cfg_of P) cfg) ->
    exists cfg', (step Is E cfg cfg')
  end.


(* _____________________________________ 
          PROOF : CORRECTNESS
   _____________________________________ *)

Theorem compiler_correct_terminates :
  forall P, (wellformed_whole_program P /\ program_defined P) ->
    ((cprogram_terminates (compile_partial_program P)) 
      <->
    (program_terminates P)).
Proof.
  intros. destruct H as [HWP Hdef].
  split.
  Case "Left".
  { intro Hterminates. unfold program_terminates. 
Admitted.

Theorem compiler_correct_diverges :
  forall P, (wellformed_whole_program P /\ program_defined P) ->
    ((cprogram_diverges (compile_partial_program P)) 
      <->
    (program_diverges P)).
Proof.
Admitted.







