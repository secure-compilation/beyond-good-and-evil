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
      0 (*???*)
  end.

(* _____________________________________ 
      COMPARTMENT MEMORY LAYOUT (2)
   _____________________________________ *)

Fixpoint EXTERNALENTRY (k:component) (P:procedure_id) :
  address :=
  match P with
  | 0 => 
    let bnum := (get_bnum k) in
    let l := length (nth (pred bnum) (get_buffers k) []) in 
    (BUFADDR k (pred bnum)) + l
  | S P' => 
    let code := admit in code (* UNCOMPLETED *)
  end.

Definition INTERNALENTRY (k:component) (P:procedure_id) : 
  address := 
  (EXTERNALENTRY k P) + 3.

(* Temporary definition *)
Definition STACKBASE (k:component) : address :=
  let code := @nil nat in
  (EXTERNALENTRY k (pred (get_pnum k))) +
  length code + 1.
(* where code = ((κ.name).(κ.pnum-1) ↦ κ.procs[κ.pnum - 1])↓*)

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

Notation "'COMPILE EXPR' ( k , e )↓ " := 
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

Notation "'COMPILE PROC' ( k , P )↓ " := 
  (compile_proc k P) (at level 0).

