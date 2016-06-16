Require Export Source.
Require Export Target.
Require Export ClassicalLogic.

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

Fixpoint update_code
  (i:nat) (i':instr) (l:code) : code :=
  match l with
  | [] => [] 
  | h::t => match i with
            | 0 => i'::t
            | S n => h :: (update_code n i' t)
            end
  end.

Definition CLEARREG : code :=
  let r_com_val := nth r_com g_regs 0 in
  let zeros := map (fun r => Const 0 r) (seq 0 nb_regs) in
  update_code r_com (Const r_com_val r_com) zeros.

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

Definition compile_component (k:option component) : 
  Target.program :=
  let Is :=
    match k with
    | Some k' => [interfaceof_C k'] 
    | None => []
    end
  in
  let mem :=
    match k with
    | Some k' =>
      [(concat (get_buffers k')) ++
      (concat (map encode_code 
        (map (compile_proc k') (generate_intlist 0 (get_pnum k'))))) ++
      [STACKBASE k'] ++
      (map (fun x => 0) (seq 0 component_allocated_memory))]
    | None => []
    end
  in
  let E :=
    match k with
    | Some k' =>
      [map (EXTERNALENTRY k') (generate_intlist 0 (get_pnum k'))]
    | None => []
    end 
  in
  (map (fun x => Some x) Is, 
   map (fun x => Some x) mem,
   map (fun x => Some x) E).


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

Definition compile_partial_program (P:Source.partial_program) : 
  Target.program :=
  let compiled_components := map compile_component P in
  fold_right fusion_compiled_program ([],[],[]) compiled_components.

Definition compile_whole_program (P:Source.program) : 
  Target.program :=
  let P' := map (fun x => Some x) P in
  let compiled_components := map compile_component P' in
  fold_right fusion_compiled_program ([],[],[]) compiled_components.

Notation "'COMPILE_PROG' P ↓ " := 
  (compile_partial_program P) (at level 0).

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
    exists cfg, (LV_multi_step Is E (LL_initial_cfg_of P) cfg)
      /\
    (state_irreducible Is E cfg) 
  end.

Definition cprogram_diverges (P:Target.program) : Prop :=
  match P with
  | (Is, mem, E) =>
    forall cfg, (LV_multi_step Is E (LL_initial_cfg_of P) cfg) ->
    exists cfg', (step Is E cfg cfg')
  end.

Lemma LL_program_behavior_exclusion :
  forall p, cprogram_terminates p /\ cprogram_diverges p
    -> False.
Proof.
  intros. destruct p as [[Is mem] E].
  destruct H as [terminates diverges].
  unfold cprogram_terminates in terminates.
  unfold cprogram_diverges in diverges.
  destruct terminates as [s H_terminates].
  destruct H_terminates as [H_term1 H_term2].
  unfold state_irreducible in H_term2. unfold not in H_term2.
  specialize (diverges s).
  assert (LV_multi_step Is E 
    (LL_initial_cfg_of (Is, mem, E)) s) as H_assert.
  { apply H_term1. }
  apply diverges in H_assert. destruct H_assert.
  apply H_term2. exists x. apply H.
Qed.

Lemma LL_program_terminates_negation :
  forall Isp mem E,
    ~(exists cfg,
      LV_multi_step Isp E (LL_initial_cfg_of (Isp, mem, E)) cfg 
      /\ state_irreducible Isp E cfg)
        ->
    (forall cfg,
    ~(LV_multi_step Isp E (LL_initial_cfg_of (Isp, mem, E)) cfg)
      \/
     ~(state_irreducible Isp E cfg)).
Proof.
  intros Isp mem E.
  intro existence. apply not_exists_dist.
  intro contra. destruct contra.
  apply de_morgan_not_or_not in H.
  apply existence. exists x.
  apply H.
Qed.

Lemma LL_program_diverges_negation :
  forall Isp mem E,
    ~(forall cfg : state,
      LV_multi_step Isp E
      (LL_initial_cfg_of (Isp, mem, E)) cfg ->
      exists cfg' : state,
      LOW_LEVEL Isp; E |- cfg ⇒ cfg')
        ->
    (exists cfg,
     LV_multi_step Isp E (LL_initial_cfg_of (Isp, mem, E)) cfg
     /\ ~(exists cfg' : state,
      LOW_LEVEL Isp; E |- cfg ⇒ cfg')).
Proof.
Admitted.

Lemma LL_program_behavior_exclusion' :
  forall p, 
    ~cprogram_terminates p -> 
    ~cprogram_diverges p
    -> False.
Proof.
  intros p doesnt_terminates doesnt_diverges.
  destruct p as [[Isp mem] E].
  unfold cprogram_terminates in doesnt_terminates.
  unfold cprogram_diverges in doesnt_diverges.
  pose (LL_program_terminates_negation Isp mem E) as lemmaT.
  pose (LL_program_diverges_negation Isp mem E) as lemmaD.
  apply lemmaD in doesnt_diverges. clear lemmaD.
  destruct doesnt_diverges as [cfg doesnt_diverges].
  apply lemmaT with (cfg := cfg) in doesnt_terminates.
  clear lemmaT.
  destruct doesnt_diverges as [H_D1 H_D2].
  destruct doesnt_terminates as [doesnt_terminates|doesnt_terminates].
  - apply doesnt_terminates in H_D1. contradiction.
  - unfold state_irreducible in doesnt_terminates.
    apply doesnt_terminates in H_D2. contradiction.
Qed.

Theorem cterminates_cdiverges_opposition :
  forall p,
  (~cprogram_terminates p) -> (cprogram_diverges p).
Proof.
  intros.
  pose (excluded_middle (cprogram_diverges p)) as EM.
  destruct EM.
  - apply H0.
  - pose (LL_program_behavior_exclusion' p
    H H0). contradiction.
Qed.


(* _____________________________________ 
          PROOF : CORRECTNESS
   _____________________________________ *)

Theorem compiler_correct_terminates :
  forall P, (wellformed_whole_program P /\ program_defined P) ->
    ((cprogram_terminates (compile_whole_program P)) 
      <->
    (program_terminates P)).
Proof.
Admitted.

Theorem compiler_correct_diverges :
  forall P, (wellformed_whole_program P /\ program_defined P) ->
    ((cprogram_diverges (compile_whole_program P)) 
      <->
    (program_diverges P)).
Proof.
Admitted.








