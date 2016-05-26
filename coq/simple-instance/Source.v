Require Export SfLib.

(* _____________________________________ 
                  SYNTAX  
   _____________________________________ *)

Definition component_id := nat.
Definition procedure_id := nat.
Definition buffer_id := nat.

Definition main_cid := 0.

(* ------- Definitions : Syntax ------- *)

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
  | ELoad : buffer_id -> expr -> expr (* b[e] *)
  | EStore : buffer_id -> expr -> expr -> expr (* b[e] := e *)
  | ECall : component_id -> procedure_id -> expr -> expr (* C.P(e) *)
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

Definition buffer : Type := list nat.

Definition procedure : Type := expr.
Definition proc_call : Type := (component_id * procedure_id).

Definition component : Type := 
  let name := nat in
  let bnum := nat in
  let buffers := list buffer in
  let pnum := nat in
  let export := nat in 
  let procedures := list procedure in
  (name * bnum * buffers * pnum * export * procedures).

Definition get_nameC (k:component) : component_id :=
  match k with
  | (name, _, _, _, _, _) => name
  end.

Definition get_bnum (k:component) : nat :=
  match k with
  | (_, bnum, _, _, _, _) => bnum
  end.

Definition get_buffers (k:component) : list buffer :=
  match k with
  | (_, _, buffers, _, _, _) => buffers
  end.

Definition get_pnum (k:component) : nat :=
  match k with
  | (_, _, _, pnum, _, _) => pnum
  end.

Definition get_exportC (k:component) : nat :=
  match k with
  | (_, _, _, _, export, _) => export
  end.

Definition get_procs (k:component) : list procedure :=
  match k with
  | (_, _, _, _, _, procs) => procs
  end.

Definition program : Type := list component.
Definition partial_program : Type := list (option component).

Definition dom_program (P:program) : list component_id :=
  map get_nameC P.

Definition proc_bodies (p:program) :=
  map get_procs p. 

Definition interface : Type :=
  let name := nat in
  let export := nat in
  let import := list proc_call in
  (name * export * import).

Definition get_name (i:interface) : component_id :=
  match i with
  | (name, _, _) => name
  end.

Definition get_import (i:interface) : 
  list proc_call :=
  match i with
  | (_, _, import) => import
  end.

Definition get_export (i:interface) : nat :=
  match i with
  | (_, export, _) => export
  end.

Definition program_interfaces : Type := list interface.

Definition dom_interfaces (Is:program_interfaces) : 
  list component_id :=
  map get_name Is.

Fixpoint procsin (e:expr) : list proc_call :=
  match e with
  | EVal i => [] 
  | EExit => []
  | ECall C P e => (C, P) :: (procsin e)
  | ELoad b e => (procsin e)
  | EBinop op e1 e2 => (procsin e1) ++ (procsin e2)
  | EStore b e1 e2 => (procsin e1) ++ (procsin e2)
  | EIfThenElse e e1 e2 => (procsin e) ++ (procsin e1) ++ (procsin e2)
  end.

Fixpoint filter_same_procsin_as (C : component_id)
  (l : list proc_call) :
  (list proc_call) :=
  match l with
  | [] => []
  | (h, h')::t => 
      if (beq_nat h C) then
        filter_same_procsin_as C t
        else
        (h, h') :: (filter_same_procsin_as C t)
  end.

Definition extprocsin (C:component_id) (e:expr) :
  list proc_call :=
  filter_same_procsin_as C (procsin e).
Fixpoint list_minus_imports 
  (l1 l2 : list proc_call) : 
  list proc_call :=
  match l1 with
  | [] => []
  | (x, y)::t => 
    if existsb (fun z => andb (beq_nat x (fst z)) (beq_nat y (snd z))) l2 then
      list_minus_imports t l2
    else
      (x, y) :: (list_minus_imports t l2)
  end.

Definition intprocsin (C:component_id) (e:expr) :
  list proc_call :=
  let ext := extprocsin C e in
  list_minus_imports (procsin e) ext.

Definition intprocsins_of_C (k:component) :
  list proc_call :=
  concat (map (intprocsin (get_nameC k)) (get_procs k)).

Fixpoint generate_import (k : component_id)
  (procedures : list expr) :
  (list proc_call) :=
  match procedures with
  | [] => []
  | e::PS => (extprocsin k e) ++ (generate_import k PS)  
  end.

Definition interfaceof_C (k : component) : interface :=
  match k with
  | (name, bnum, buffers, pnum, export, procedures) => 
    (name, export, generate_import (get_nameC k) (get_procs k))
  end.

Definition interfaceof_P (p : program) : program_interfaces :=
  map interfaceof_C p.

Fixpoint bufsin (e:expr) : list buffer_id :=
  match e with
  | EVal _ => []
  | EExit => []
  | ECall C P e => bufsin e
  | ELoad b e => [b] ++ (bufsin e)
  | EStore b e1 e2 => [b] ++ (bufsin e1) ++ (bufsin e2)
  | EBinop _ e1 e2 => (bufsin e1) ++ (bufsin e2)
  | EIfThenElse e e1 e2 => (bufsin e) ++ (bufsin e1) ++ (bufsin e2) 
  end.

Definition bufsin_in_C (k:component) : list buffer_id :=
  match k with
  | (_, _, _, _, procs) => concat (map bufsin procs) 
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
  | CHoleLoad : buffer_id -> flatevalcon (* b[□] *)
  | CHoleStore : buffer_id -> expr -> flatevalcon (* b[□] := e *)
  | CStoreHole : buffer_id -> nat -> flatevalcon (* b[i] := □ *)
  | CCallHole : component_id -> procedure_id -> flatevalcon. (* C.P(□) *)

(* Used for the well-formedness of flatevalcon. It's a 
approximation for the search of procedure calls with
conservation of the structure of the flatevalcon expression *)
Fixpoint flatevalcon_to_expr (E:flatevalcon) : expr :=
  match E with
  | CHoleOp op e => EBinop op e e
  | COpHole n op => EBinop op (EVal n) (EVal n)
  | CIfHoleThenElse e e' => EIfThenElse e e' e'
  | CHoleLoad b => ELoad b (EVal 0)
  | CHoleStore b e => EStore b e e
  | CStoreHole b i => EStore b (EVal i) (EVal i)
  | CCallHole C P => ECall C P EExit 
  end.

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
  | Call : component_id -> nat -> continuations -> call.

Definition call_stack :=
  list call.

Definition state :=
  list (list buffer).

Fixpoint update_value
  (i:nat) (i':nat) (l:buffer) : buffer :=
  match l with
  | [] => [] 
  | h::t => match i with
            | 0 => i'::t
            | S n => h :: (update_value n i' t)
            end
  end.

Fixpoint update_buffer
  (b:buffer_id) (i:nat) (i':nat) (l:list buffer) : list buffer :=
  match l with
  | [] => []
  | h::t => match b with
            | 0 => (update_value i i' h) :: t
            | S b' => h::(update_buffer b' i i' t)
            end
  end.

Fixpoint update_component
  (C:component_id) (b:buffer_id) (i:nat) (i':nat) (s:state) : state :=
  match s with
  | [] => []
  | h::t => match C with
            | 0 => (update_buffer b i i' h) :: t
            | S C' => h::(update_component C' b i i' t)
            end 
  end.

Definition update_state
  (C:component_id) (b:buffer_id) (i:nat) (i':nat) (s:state) : state :=
  update_component C b i i' s.

Definition cfg : Type :=
  component_id * state * call_stack * continuations * expr.

Definition context :=
  list (list procedure).

Definition procbodies (P:program) : context :=
  map (get_procs) P.

(* ------- Definitions : definedness ------- *)

Definition component_defined (C:component_id) 
  (X:Type) (D:list X) : bool :=
  let l := (length D) in
  if andb (ble_nat C l) (negb (beq_nat C l)) then
    true
  else
    false.

Definition procedure_defined (C:component_id) 
  (P:procedure_id) (X:Type) (D:list X) : bool :=
  let l := (length D) in
  if (andb (ble_nat P l) (negb (beq_nat P l))) then
    true
  else
    false.

Definition procedure_defined_interfaces (C:component_id) 
  (P:procedure_id) (Is:program_interfaces) : bool :=
  let exp := get_export (nth C Is (0,0,[])) in
  if (andb (ble_nat P exp) (negb (beq_nat P exp))) then
    true
  else
    false.

Definition buffer_defined (C:component_id) 
  (b:buffer_id) (s:state) : bool :=
  let l := (length (nth C s [])) in
  if (andb (ble_nat b l) (negb (beq_nat b l))) then
    true
  else
    false.

Definition value_defined (C:component_id) (b:buffer_id) 
  (i:nat) (s:state) : bool :=
  let l := (length (nth b (nth C s []) [])) in
  if (andb (ble_nat i l) (negb (beq_nat i l))) then
    true
  else
    false.

(* Undefinedness *)

Definition component_undefined (C:component_id) 
  (X:Type) (D:list X)
  : bool :=
  negb (component_defined C X D).

Definition procedure_undefined (C:component_id) 
  (P:procedure_id) (X:Type) (D:list X) : bool :=
  negb (procedure_defined C P X D).

Definition buffer_undefined (C:component_id) 
  (b:buffer_id) (s:state) : bool :=
  negb (buffer_defined C b s).

Definition value_undefined (C:component_id) (b:buffer_id) 
  (i:nat) (s:state) : bool :=
  negb (value_defined C b i s).

(* ------- Definitions : fetch functions ------- *)

Definition fetch_context 
  (C':component_id) (P':procedure_id) (D:context) : expr :=
  nth P' (nth C' D []) exit.

Definition fetch_state (C:component_id) (b:buffer_id) 
  (i:nat) (s:state) :=
  nth i (nth b (nth C s []) []) 0.

(* ------- Definitions : special configurations ------- *)

Definition generate_state (P:program) : state :=
  map get_buffers P.

Definition initial_cfg_of (P:program) : cfg :=
  let s := generate_state P in
  let initial_proc := nth 0 (get_procs (nth main_cid P (0,0,[],0,0,[]))) EExit in
  (main_cid, (update_state main_cid 0 0 0 s), [], [], initial_proc).

Inductive final_cfg : cfg -> Prop :=
  | final_value : forall C s i, final_cfg (C, s, [], [], EVal i)
  | final_exit  : forall C s d K, final_cfg (C, s, d, K, EExit).

(* ------- Definitions : small-step semantic definition ------- *)

Reserved Notation "D ⊢ e '⇒' e'" (at level 40).
Inductive small_step (D: context) : cfg -> cfg -> Prop :=
  (* S_BinOp_Push *)
  | S_BinOp_Push : forall C s d K e1 e2 op,
    D ⊢ (C, s, d, K, EBinop op e1 e2) ⇒
    (C, s, d, (CHoleOp op e2)::K, e1)
  (* S_BinOp_Switch *)
  | S_BinOp_Switch : forall C s d e2 K i1 op,
    D ⊢ (C, s, d, (CHoleOp op e2)::K, EVal i1) ⇒
    (C, s, d, (COpHole i1 op)::K, e2)
  (* S_BinOp_Pop *)
  | S_BinOp_Pop : forall C s d i1 op K i2,
    D ⊢ (C, s, d, (COpHole i1 op)::K, EVal i2) ⇒
    (C, s, d, K, eval_binop (op, i1, i2))
  (* S_If_Push *)
  | S_If_Push : forall C s d K e e1 e2,
    D ⊢ (C, s, d, K, (IFB e THEN e1 ELSE e2)) ⇒
    (C, s, d, (IFB □ THEN e1 ELSE e2)::K, e)
  (* S_If_Pop_NZ *)
  | S_If_Pop_NZ : forall C s d K e1 e2 i,
    ~(i=0) -> D ⊢ (C, s, d, (IFB □ THEN e1 ELSE e2)::K, EVal i) ⇒
    (C, s, d, K, e1)
  (* S_If_Pop_Z *)
  | S_If_Pop_Z : forall C s d e1 e2 K,
    D ⊢ (C, s, d, (IFB □ THEN e1 ELSE e2)::K, EVal 0) ⇒
    (C, s, d, K, e2)
  (* S_Read_Push *)
  | S_Read_Push : forall C s d K b e,
    D ⊢ (C, s, d, K, ELoad b e) ⇒
    (C, s, d, (CHoleLoad b)::K, e)
  (* S_Read_Pop *)
  | S_Read_Pop : forall C s d b K i,
    (value_defined C b i s = true) ->
    D ⊢ (C, s, d, (CHoleLoad b)::K, EVal i) ⇒
    (C, s, d, K, EVal (fetch_state C b i s))
  (* S_Write_Push *)
  | S_Write_Push : forall C s d K b e1 e2,
    D ⊢ (C, s, d, K, EStore b e1 e2) ⇒
    (C, s, d, (CHoleStore b e2)::K, e1)
  (* S_Write_Swap *)
  | S_Write_Swap : forall C s d b e2 K i,
    D ⊢ (C, s, d, (CHoleStore b e2)::K, EVal i) ⇒
    (C, s, d, (CStoreHole b i)::K, e2)
  (* S_Write_Pop *)
  | S_Write_Pop : forall C s d b i K i',
    (value_defined C b i s = true) ->
    D ⊢ (C, s, d, (CStoreHole b i)::K, EVal i') ⇒
    (C, (update_state C b i i' s), d, K, EVal i')
  (* S_Call_Push *)
  | S_Call_Push : forall C s d K C' P' e,
    D ⊢ (C, s, d, K, ECall C' P' e) ⇒
    (C, s, d, (CCallHole C' P')::K, e)
  (* S_Call_Pop *)
  | S_Call_Pop : forall C' P' C s d K ia,
    let ep := fetch_context C' P' D in     
    D ⊢ (C, s, d, (CCallHole C' P')::K, EVal ia) ⇒
    (C', (update_state C' 0 0 ia s), (Call C (fetch_state C 0 0 s) K)::d, [], ep)
  (* S_Return *)
  | S_Return : forall C s C' ia K d i,
    D ⊢ (C, s, (Call C' ia K)::d, [], EVal i) ⇒
    (C', (update_state C' 0 0 ia s), d, K, EVal i)
  where "D ⊢ e '⇒' e'" := (small_step D e e').

(* ------- Definitions : small-step multi-reduction ------- *)

Notation "D ⊢ e '⇒*' e'" := (multi (small_step D) e e') (at level 40).

(* ------- Definitions : small-step irreducibility ------- *)

Reserved Notation "D ⊢ cfg '↛'" (at level 40).
Inductive cfg_irreducible (D:context) : cfg -> Prop :=
  | S_Irreducible : forall cfg cfg',
    ~(D ⊢ cfg ⇒ cfg') ->
    D ⊢ cfg ↛
  where "D ⊢ cfg '↛'" := (cfg_irreducible D cfg).

(* ---- Undefined behaviors ---- *)

Inductive undefined_cfg : context -> cfg -> Prop :=
  | undef_load : forall C s d b i K D, 
    (value_undefined C b i s = true) ->
    undefined_cfg D (C, s, d, (CHoleLoad b)::K, EVal i)
  | undef_store  : forall C s d b K i i' D,
    (value_undefined C b i s = true) ->
    undefined_cfg D (C, s, d, (CStoreHole b i)::K, EVal i').

Example undefined_cfg1 :
  undefined_cfg [] (0, [], [], (CHoleLoad 0)::[], EVal 1).
Proof.
  constructor.
  unfold value_undefined.
  unfold value_defined.
  reflexivity.
Qed.

Example buff_def1 : value_undefined 0 0 4 [[];[]] = true.
Proof.
  unfold value_undefined.
  unfold value_defined.
  reflexivity.
Qed.

Example buff_def2 : value_defined 0 0 1 [[[1;2;3];[];[]]] = true.
Proof.
  unfold value_defined.
  simpl. reflexivity.
Qed.

(* _____________________________________ 
           EVALUATION FUNCTION
   _____________________________________ *)

Definition basic_eval_cfg (D:context) (c:cfg) : cfg :=
  match c with
  (* S_BinOp_Push *)
  | (C, s, d, K, EBinop op e1 e2) =>
    (C, s, d, (CHoleOp op e2) :: K, e1)
  (* S_BinOp_Switch *)
  | (C, s, d, (CHoleOp op e2) :: K, EVal i1) =>
    (C, s, d, (COpHole i1 op) :: K, e2)
  (* S_BinOp_Pop *)
  | (C, s, d, (COpHole i1 op) :: K, EVal i2) =>
    (C, s, d, K, (eval_binop (op, i1, i2)))
  (* S_If_Push *)
  | (C, s, d, K, (EIfThenElse e1 e2 e3)) =>
    (C, s, d, (CIfHoleThenElse e2 e3) :: K, e1)
  (* S_If_Pop_NZ *)
  | (C, s, d, (CIfHoleThenElse e2 e3) :: K, EVal 0) =>
    (C, s, d, K, e3)
  (* S_If_Pop_Z *)
  | (C, s, d, (CIfHoleThenElse e2 e3) :: K, EVal _) =>
    (C, s, d, K, e2)
  (* S_Read_Push *)
  | (C, s, d, K, (ELoad b e)) => 
    (C, s, d, (CHoleLoad b) :: K, e)
  (* S_Read_Pop *)
  | (C, s, d, (CHoleLoad b) :: K, EVal i) =>
    if (value_defined C b i s) then
      (C, s, d, K, EVal (fetch_state C b i s)) 
    else c
  (* S_Write_Push *)
  | (C, s, d, K, (EStore b e1 e2)) =>
    (C, s, d, (CHoleStore b e2) :: K, e1)
  (* S_Write_Swap *)
  | (C, s, d, (CHoleStore b e2) :: K, EVal i1) =>
    (C, s, d, (CStoreHole b i1) :: K, e2)
  (* S_Write_Pop *)
  | (C, s, d, (CStoreHole b i1) :: K, EVal i2) =>
    if (value_defined C b i1 s) then
      (C, update_state C b i1 i2 s, d, K, EVal i2)
    else c
  (* S_Call_Push *)
  | (C, s, d, K, (ECall C' P' e)) =>
      (C, s, d, (CCallHole C' P') :: K, e)
  (* S_Call_Pop *)
  | (C, s, d, (CCallHole C' P') :: K, EVal i) =>
    let s' := (update_state C' 0 0 i s) in 
    let e' := (fetch_context C' P' D) in
      (C', s', ((Call C (fetch_state C 0 0 s) K) :: d), [], e')
  (* S_Return *)
  | (C, s, (Call C' ia K) :: d', [], EVal i) =>
    (C', update_state C' 0 0 ia s, d', K, EVal i)
  (* Final cfg *)
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
  eapply multi_step. apply S_Call_Pop.
  eapply multi_step.
    subcompute (fetch_context 1 0 context_fact).
    apply S_If_Push.
  eapply multi_step. apply S_BinOp_Push. 
  eapply multi_step. apply S_Read_Push.
  eapply multi_step. apply S_Read_Pop. reflexivity.
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
  eapply multi_step. apply S_Read_Pop. reflexivity.
  eapply multi_step. 
    subcompute (fetch_state 1 0 0 (update_state 1 0 0 2 state_fact)).
    apply S_BinOp_Switch.
  eapply multi_step. apply S_BinOp_Pop.
  eapply multi_step.
    subcompute (eval_binop (EMinus, 2, 1)). 
    apply S_Call_Pop.
  eapply multi_step.
    subcompute ((fetch_state 1 0 0 state_fact)).
    subcompute (fetch_context 1 0 context_fact).
    apply S_If_Push.
  eapply multi_step. apply S_BinOp_Push. 
  eapply multi_step. apply S_Read_Push.
  eapply multi_step. apply S_Read_Pop. reflexivity.
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
  eapply multi_step. apply S_Read_Pop. reflexivity.
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
     WELL-FORMEDNESS : PROGRAM SCOPE
   _____________________________________ *)

(* ---- Useful functions ---- *)

Definition compsImport (l:list proc_call) :=
   map fst l.

Definition compsComponent (Cs:list component) :=
  map get_nameC Cs.

Definition compsInterface (Is:program_interfaces) :=
  map get_name Is.

Definition compsProgram (P:program) :=
  map get_nameC P.

(* Lower bound included, upper bound exluded *)
Fixpoint generate_intlist (min:nat) (max:nat) : list nat :=
  match max with
  | 0 => []
  | S n' => if beq_nat (S n') min then
                []
            else
               (generate_intlist min n') ++ [n']
  end.

(* ---- Well-formedness invariants ---- *)

Definition component_invariant : Type :=
  let name := nat in
  let pnum := nat in
  let bnum := nat in
  let blens := list nat in
  (name * pnum * bnum * blens).

Definition get_nameN (n:component_invariant) : nat :=
  match n with
  | (name, _, _, _) => name
  end.

Definition get_pnumN (n:component_invariant) : nat :=
  match n with
  | (_, pnum, _, _) => pnum
  end.

Definition get_bnumN (n:component_invariant) : nat :=
  match n with
  | (_, _, bnum, _) => bnum
  end.

Definition get_blens (n:component_invariant) : list nat :=
  match n with
  | (_, _, _, blens) => blens
  end.

Definition partial_program_invariant : Type :=
  list component_invariant.

Definition wfinv_of_C (k:component) : component_invariant :=
  match k with
  | (name, bnum, buffers, pnum, _, _) =>
    let blens := (map (@length nat) buffers) in
    (name, pnum, bnum, blens)
  end.

Definition wfinv_of_P (P:program) : partial_program_invariant :=
  map wfinv_of_C P.


(* ---- Well-formedness of an interface ---- *)
Reserved Notation "'INTERFACE' Is |- i 'wellformed'" (at level 40).
Inductive wellformed_interface (Is : program_interfaces) : 
  interface -> Prop :=
  | WF_interface : forall i,
    let not_i := (fun i' => (negb (beq_nat (get_name i) i'))) in
    incl (compsImport (get_import i)) (filter (not_i) (compsInterface Is)) ->    
    (forall C P, In (C,P) (get_import i) ->
      let exp := (get_export (nth C Is (0, 0, []))) in 
       In P (generate_intlist 0 exp)) ->
    (forall C P, In (C,P) (get_import i) ->
      procedure_defined_interfaces C P Is = true
        /\ 
      component_defined C interface Is = true) ->
    INTERFACE Is |- i wellformed 
  where "'INTERFACE' Is |- i 'wellformed'" := (wellformed_interface Is i).

(* ---- Well-formedness of a program interface ---- *)
Reserved Notation "'INTERFACES' |- Is 'wellformed'" (at level 40).
Inductive wellformed_interfaces : program_interfaces -> Prop :=
  | WF_interfaces : forall Is,
    (forall i, (In i Is) -> wellformed_interface Is i) ->
    (forall i1 i2, (In i1 Is /\ In i2 Is) -> get_name i1 <> get_name i2) ->
    (exists i', (In i' Is) /\ (get_name i' = main_cid /\ (0 <> (get_export i')))
      /\ procedure_defined_interfaces main_cid 0 Is = true) ->
    INTERFACES |- Is wellformed 
  where "'INTERFACES' |- Is 'wellformed'" := (wellformed_interfaces Is).

(* ---- Compatibility between interfaces ---- *)
Reserved Notation "'COMPATIBILITY' i1 ⊆ i2" (at level 40).
Inductive compatibility_interface : interface -> interface -> Prop :=
  | compatible_interface : forall i1 i2,
    (get_name i1 = get_name i2) ->
    (incl (get_import i1) (get_import i2)) ->
    (get_export i1 = get_export i2) ->
    COMPATIBILITY i1 ⊆ i2
  where "'COMPATIBILITY' i1 ⊆ i2" := (compatibility_interface i1 i2).

(* ---- Well-formedness of a component ---- *)
Reserved Notation "'COMPONENT' Is |- k 'wellformed'" (at level 40).
Inductive wellformed_component (Is:program_interfaces) : component -> Prop :=
  | WF_component : forall k,
    component_defined (get_nameC k) interface Is = true ->
    COMPATIBILITY (interfaceof_C k) ⊆ (nth (get_nameC k) Is (0, 0, [])) ->
    (forall C P, In (C,P) (intprocsins_of_C k) -> 
      In P (generate_intlist 0 (get_pnum k))) ->
    (incl (bufsin_in_C k) (generate_intlist 0 (get_bnum k))) ->
    ble_nat (get_exportC k) (get_pnum k) = true -> 
    (ble_nat 1 (get_bnum k) = true /\ ble_nat 1 (length (nth 0 (get_buffers k) [])) = true) ->    
    COMPONENT Is |- k wellformed
  where "'COMPONENT' Is |- k 'wellformed'" := (wellformed_component Is k).

(* ---- Well-formedness : alternative definitions ---- *)
Inductive wellformed_expr_alt (i:interface) (n:component_invariant) : 
  expr -> Prop :=
  | WF_expr_alt_EVal : forall v,
    wellformed_expr_alt i n (EVal v)
  | WF_expr_alt_EBinop : forall op e1 e2,
    wellformed_expr_alt i n e1 ->
    wellformed_expr_alt i n e2 ->
    wellformed_expr_alt i n (EBinop op e1 e2) 
  | WF_expr_alt_EIfThenElse : forall e e1 e2,
    wellformed_expr_alt i n e ->
    wellformed_expr_alt i n e1 ->
    wellformed_expr_alt i n e2 ->
    wellformed_expr_alt i n (EIfThenElse e e1 e2)
  | WF_expr_alt_ELoad : forall b e,
    let l := (get_bnumN n) in
    andb (ble_nat b l) (negb (beq_nat b l)) = true ->
    wellformed_expr_alt i n e ->
    wellformed_expr_alt i n (ELoad b e)
  | WF_expr_alt_EStore : forall b e1 e2,
    let l := (get_bnumN n) in
    andb (ble_nat b l) (negb (beq_nat b l)) = true ->
    wellformed_expr_alt i n e1 ->
    wellformed_expr_alt i n e2 ->
    wellformed_expr_alt i n (EStore b e1 e2)
  | WF_expr_alt_ECall : forall C P e,
    (let l := (get_pnumN n) in
     let l' := (get_export i) in
    let proc_defined_in := andb (ble_nat P l) (negb (beq_nat P l)) = true in
    let proc_defined_in' := andb (ble_nat P l') (negb (beq_nat P l')) = true in
    (C = (get_name i) /\ proc_defined_in /\ proc_defined_in') \/
    let proc_defined_out := In (C,P) (get_import i) in
     (C <> (get_name i) /\ proc_defined_out)) ->
    wellformed_expr_alt i n e ->
    wellformed_expr_alt i n (ECall C P e)
  | WF_expr_alt_EExit : 
    wellformed_expr_alt i n (EExit).

Inductive wellformed_component_alt (Is:program_interfaces) : component -> Prop :=
  | WF_component_alt : forall k,
    (component_defined (get_nameC k) interface Is = true) ->
    (forall P, 
      let i := (nth (get_nameC k) Is (0,0,[])) in
      let n := wfinv_of_C k in
      ((procedure_defined_interfaces (get_nameC k) P Is = true)
        ->
      (wellformed_expr_alt i n (nth P (get_procs k) EExit)))) ->
    (ble_nat (get_exportC k) (get_pnum k) = true) -> 
    (ble_nat 1 (get_bnum k) = true /\ ble_nat 1 (length (nth 0 (get_buffers k) [])) = true) ->    
    wellformed_component_alt Is k.

(* ---- Well-formedness of a partial program ---- *)
Reserved Notation "'PARTIAL_PROGRAM' Is |- p 'wellformed'" (at level 40).
Inductive wellformed_partial_program (Is:program_interfaces) : program -> Prop :=
  | WF_partial_program : forall p,
    (forall C k, 
      (In k p -> wellformed_component_alt Is k) 
        /\
      ((In k p) /\ (get_nameC k = C) -> (get_nameC (nth C p (0, 0, [], 0, 0, []))) = C)
        /\
      (In (nth C p (0, 0, [], 0, 0, [])) p <-> (get_nameC (nth C p (0, 0, [], 0, 0, []))) = C)
    ) ->
    PARTIAL_PROGRAM Is |- p wellformed
  where "'PARTIAL_PROGRAM' Is |- p 'wellformed'" := (wellformed_partial_program Is p).

(* ---- Well-formedness of a whole program ---- *)
Reserved Notation "'WHOLE_PROGRAM' |- p 'wellformed'" (at level 40).
Inductive wellformed_whole_program : program -> Prop :=
  | WF_whole_program : forall p,
    INTERFACES |- (interfaceof_P p) wellformed ->
    PARTIAL_PROGRAM (interfaceof_P p) |- p wellformed -> 
    WHOLE_PROGRAM |- p wellformed
  where "'WHOLE_PROGRAM' |- p 'wellformed'" := (wellformed_whole_program p).


(* _____________________________________ 
       WELL-FORMEDNESS : CFG SCOPE
   _____________________________________ *)

(* ---- Well-formedness of an expression ---- *)
Reserved Notation "'EXPR' i n |- e 'wellformed'" (at level 40).
Inductive wellformed_expr (i:interface) (n:component_invariant) : 
  expr -> Prop :=
  | WF_expr : forall e,
    incl (extprocsin (get_name i) e) (get_import i) ->
    (forall C P, In (C,P) (intprocsin (get_name i) e) -> 
      In P (generate_intlist 0 (get_pnumN n))) -> 
    incl (bufsin e) (generate_intlist 0 (get_bnumN n)) ->    
    wellformed_expr i n e
  where "'EXPR' i n |- e 'wellformed'" := (wellformed_expr i n e).

(* ---- Well-formedness of a flat evaluation context ---- *)
Reserved Notation "'FLATEVALCON' i n |- E 'wellformed'" (at level 40).
Inductive wellformed_flatevalcon (i:interface) (n:component_invariant) : 
  flatevalcon -> Prop :=
  | WF_flatevalcon : forall E,
    incl (extprocsin (get_name i) (flatevalcon_to_expr E)) (get_import i) ->
    (forall C P, In (C,P) (intprocsin (get_name i) (flatevalcon_to_expr E)) -> 
      In P (generate_intlist 0 (get_pnumN n))) ->  
    incl (bufsin (flatevalcon_to_expr E)) (generate_intlist 0 (get_bnumN n)) ->    
    wellformed_flatevalcon i n E
  where "'FLATEVALCON' i n |- E 'wellformed'" := (wellformed_flatevalcon i n E).

Inductive wellformed_flatevalcon_alt (i:interface) 
  (n:component_invariant) : flatevalcon -> Prop :=
  | WF_flatevalcon_alt_CHoleOp : forall op e2,
    wellformed_expr_alt i n e2 ->
    wellformed_flatevalcon_alt i n (CHoleOp op e2)
  | WF_flatevalcon_alt_COpHole : forall op v,
    wellformed_flatevalcon_alt i n (COpHole v op)
  | WF_flatevalcon_alt_CIfHoleThenElse : forall e1 e2,
    wellformed_expr_alt i n e1 ->
    wellformed_expr_alt i n e2 ->
    wellformed_flatevalcon_alt i n (CIfHoleThenElse e1 e2)
  | WF_flatevalcon_alt_CHoleLoad : forall b,
    let l := (get_bnumN n) in
    andb (ble_nat b l) (negb (beq_nat b l)) = true -> 
    wellformed_flatevalcon_alt i n (CHoleLoad b)
  | WF_flatevalcon_alt_CHoleStore : forall b e,
    let l := (get_bnumN n) in
    andb (ble_nat b l) (negb (beq_nat b l)) = true -> 
    wellformed_expr_alt i n e ->
    wellformed_flatevalcon_alt i n (CHoleStore b e)
  | WF_flatevalcon_alt_CStoreHole : forall b v,
    let l := (get_bnumN n) in
    andb (ble_nat b l) (negb (beq_nat b l)) = true -> 
    wellformed_flatevalcon_alt i n (CStoreHole b v)
  | WF_flatevalcon_alt_CCallHole : forall C P,
    (let l := (get_pnumN n) in
     let l' := (get_export i) in
    let proc_defined_in := andb (ble_nat P l) (negb (beq_nat P l)) = true in
    let proc_defined_in' := andb (ble_nat P l') (negb (beq_nat P l')) = true in
    (C = (get_name i) /\ proc_defined_in /\ proc_defined_in') \/
    let proc_defined_out := In (C,P) (get_import i) in
     (C <> (get_name i) /\ proc_defined_out)) ->
    wellformed_flatevalcon_alt i n (CCallHole C P).

(* ---- Well-formedness of a continuation ---- *)
Reserved Notation "'CONTINUATIONS' i n |- K 'wellformed'" (at level 40).
Inductive wellformed_continuations (i:interface) (n:component_invariant) : 
  continuations -> Prop :=
  | WF_empty_continuations :
    wellformed_continuations i n []
  | WF_continuations : forall E K,
    (wellformed_flatevalcon_alt i n E) ->
    (wellformed_continuations i n K) ->
    (wellformed_continuations i n (E::K))
  where "'CONTINUATIONS' i n |- K 'wellformed'" := (wellformed_continuations i n K).

(* ---- Well-formedness of a callstack ---- *)
Reserved Notation "'CALLSTACK' i n |- K 'wellformed'" (at level 40).
Inductive wellformed_callstack (Is:program_interfaces) 
  (G:partial_program_invariant) : call_stack -> Prop :=
  | WF_empty_callstack :
    wellformed_callstack Is G []
  | WF_callstack : forall C d i K,
    component_defined C interface Is = true ->
    (wellformed_continuations (nth C Is (0,0,[])) (nth C G (0,0,0,[])) K) ->
    (wellformed_callstack Is G d) ->
    (wellformed_callstack Is G ((Call C i K)::d))
  where "'CALLSTACK' Is G |- d 'wellformed'" := (wellformed_callstack Is G d).

(* ---- Well-formedness of a state ---- *)
Reserved Notation "'STATE' G |- s 'wellformed'" (at level 40).
Inductive wellformed_state (G:partial_program_invariant) : 
  state -> Prop :=
  | WF_state : forall s,
    (forall n, (In n G) ->
     (forall b i,
      let l := get_bnumN n in
      let l' := (nth b (get_blens n) 0) in 
      (andb (ble_nat b l) (negb (beq_nat b l)) = true) /\
      (andb (ble_nat i l') (negb (beq_nat i l')) = true) 
        ->
      (value_defined (get_nameN n) b i s = true))) ->
    wellformed_state G s
  where "'STATE' G |- s 'wellformed'" := (wellformed_state G s).

(* ---- Well-formedness of a configuration ---- *)
Reserved Notation "'CFG' Is G |- c 'wellformed'" (at level 40).
Inductive wellformed_cfg (Is:program_interfaces)
  (G:partial_program_invariant) : cfg -> Prop :=
  | WF_cfg : forall C s d K e,
    wellformed_state G s ->
    wellformed_callstack Is G d ->
    component_defined C interface Is = true ->
    wellformed_continuations (nth C Is (0,0,[])) (nth C G (0,0,0,[])) K ->
    wellformed_expr_alt (nth C Is (0,0,[])) (nth C G (0,0,0,[])) e ->
    wellformed_cfg Is G (C, s, d, K, e)
  where "'CFG' Is G |- c 'wellformed'" := (wellformed_state Is G c).

(* ------- Definitions : definedness of programs ------- *)

Inductive program_undefined (P:program) : Prop :=
  | P_Undef : 
    wellformed_whole_program P ->
    (procbodies P) ⊢ (initial_cfg_of P) ↛ ->
    program_undefined P.

Definition program_defined (P:program) : Prop :=
  ~(program_undefined P).     

(* _____________________________________ 
        PROOF : PARTIAL TYPE SAFETY
   _____________________________________ *)


Lemma interfacename_is_componentname :
  forall k,
  get_nameC k = get_name (interfaceof_C k).
Proof.
  intros.
  destruct k as [[[[k1 k2] k3] k4] k5].
  destruct k1; destruct k2; destruct k3;
  destruct k4; destruct k5; simpl; reflexivity.
Qed.

Lemma component_index_correspondance_eq' :
  forall C P,
  wellformed_whole_program P ->
  In (nth C P (0, 0, [], 0, 0, [])) P ->
  (get_nameC (nth C P (0, 0, [], 0, 0, []))) = C.
Proof.
  intros C P HWP H. inversion HWP.
  inversion H1. specialize (H3 C (nth C P (0, 0, [], 0, 0, []))).
  destruct H3. destruct H3. destruct H5.
  apply H. destruct H5. destruct H9.
  apply H9 in H. apply H.
Qed.

Lemma interface_component_id_correspondance :
  forall P, wellformed_whole_program P ->
  forall C i,
  (In i (interfaceof_P P) /\ get_name i = C -> 
   exists k, In k P /\ get_nameC k = C).
Proof.
  intros.
  destruct H0 as [Hin Hname].
  unfold interfaceof_P in Hin.
  pose (in_map_iff interfaceof_C P i) as lemma.
  destruct lemma.
  apply H0 in Hin.
  destruct Hin.
  exists x. destruct H2.
  split. apply H3.
  rewrite <- Hname.
  rewrite <- H2.
  apply interfacename_is_componentname.
Qed.

Lemma component_index_correspondance_eq :
  forall k P C, wellformed_whole_program P ->
  (In k P /\ get_nameC k = C) ->
  (get_nameC (nth C P (0, 0, [], 0, 0, []))) = C.
Proof.
  intros. inversion H.
  inversion H2. specialize (H4 C k).
  destruct H4. assert (H0' := H0).
  destruct H0'. destruct H6.
  apply H6 in H0. apply H0.
Qed.

Lemma interface_component_index_correspondance_eq :
  forall i P C, wellformed_whole_program P ->
  (In i (interfaceof_P P) /\ get_name i = C) ->
  (get_nameC (nth C P (0, 0, [], 0, 0, []))) = C.
Proof.
  intros i P C HWP H.
  apply (interface_component_id_correspondance P HWP) in H.
  destruct H.
  apply component_index_correspondance_eq in H.
  apply H. apply HWP.
Qed.

Lemma sameinterface_means_samename :
  forall P, wellformed_whole_program P ->
  forall k1 k2, (interfaceof_C k1) = (interfaceof_C k2) ->
  get_name (interfaceof_C k1) = get_name (interfaceof_C k2).
Proof.
  intros. rewrite H0. reflexivity.
Qed.

Lemma component_index_correspondance_eq'' :
  forall C P,
  wellformed_whole_program P ->
  In (nth C (interfaceof_P P) (0, 0, [])) (interfaceof_P P) ->
  (get_name (nth C (interfaceof_P P) (0, 0, []))) = C.
Proof.
  intros. 
  (* Transposition of the goal *)
  unfold interfaceof_P.
  pose (map_nth interfaceof_C P (0, 0, [], 0, 0, []) C) as lemma.
  simpl in lemma. rewrite lemma. rewrite <- interfacename_is_componentname.
  (* Transposition of the hypothesis *)
  assert (In (nth C (interfaceof_P P) (0, 0, []))
       (interfaceof_P P) -> In (nth C P (0, 0, [], 0, 0, [])) P) as Hassert.
  Case "Proof of assertion".
  { intro. unfold interfaceof_P in H1. rewrite lemma in H1.
    pose (in_map_iff interfaceof_C P (interfaceof_C (nth C P (0, 0, [], 0, 0, [])))).
    destruct i. apply H2 in H1. destruct H1. destruct H1.
    clear H3. clear H2.
    unfold interfaceof_P in H0. rewrite lemma in H0.
    assert (H0' := H0). rewrite <- H1 in H0'.
    inversion H. inversion H2. 
    specialize (H7 (interfaceof_C (nth C P (0, 0, [], 0, 0, [])))
      (interfaceof_C x)).
    assert (In (interfaceof_C (nth C P (0, 0, [], 0, 0, []))) (interfaceof_P P) /\
     In (interfaceof_C x) (interfaceof_P P)) as Hassert.
    SCase "Injectivity of interfaceof_C".
    { split. apply H0. apply H0'. }
    apply H7 in Hassert. unfold not in Hassert. 
    apply (sameinterface_means_samename P H) in H1.
    symmetry in H1. apply Hassert in H1. contradiction.
  } 
  apply Hassert in H0. apply component_index_correspondance_eq'.
  apply H. apply H0.
Qed.

Lemma negation_transfert :
  forall a b, negb a = b <-> a = negb b.
Proof.
  intros.
  split.
  Case "->".
    intro.
    destruct a; destruct b;
    try (inversion H);
    try (reflexivity).
  Case "<-".
    intro.
    destruct a; destruct b;
    try (inversion H);
    try (reflexivity).
Qed.

Lemma blenat_implies_leq :
  forall n m, (ble_nat n m) && negb (beq_nat n m) = true -> (n < m).
Proof.
  intro n. induction n as [|n'].
  Case "n = 0".
  { intros. destruct m. inversion H. apply neq_0_lt.
    unfold not. intro. inversion H0.
  }
  Case "n = S n'".
  { intros. destruct m. inversion H. apply lt_n_S.
    apply IHn'. apply andb_true in H. destruct H.
    simpl in H. rewrite H. apply negation_transfert in H0.
    simpl in H0. rewrite H0. reflexivity.
  }
Qed. 

Lemma interface_index_correspondance_eq :
  forall P, wellformed_whole_program P ->
  forall C, 
  component_defined C interface (interfaceof_P P) = true ->
  get_name (nth C (interfaceof_P P) (0, 0, [])) = C.
Proof.
  intros. unfold interfaceof_P.
  assert (In (nth C (interfaceof_P P) (0, 0, [])) (interfaceof_P P)) as Hassert.
  Case "Proof of assertion".
  { unfold component_defined in H0. apply andb_true in H0.
    destruct H0. apply blenat_implies_leq in H0.
    pose (@nth_In interface C (interfaceof_P P) (0, 0, [])) as lemma.
    apply lemma in H0. apply H0.
  }
  apply component_index_correspondance_eq''. apply H.
  apply Hassert.
Qed.

Lemma component_index_correspondance_in :
  forall C P,
  wellformed_whole_program P ->
  (get_nameC (nth C P (0, 0, [], 0, 0, []))) = C ->
  In (nth C P (0, 0, [], 0, 0, [])) P.
Proof.
  intros. inversion H. inversion H2.
  specialize (H4 C (nth C P (0, 0, [], 0, 0, []))).
  destruct H4. destruct H6. destruct H7.
  apply H8. apply H0.
Qed.

Lemma correct_program_contains_main :
  forall P, wellformed_whole_program P ->
  In (nth main_cid P (0, 0, [], 0, 0, [])) P.
Proof.
  intros P HWP. inversion HWP.
  inversion H.
  destruct H4; destruct H4; destruct H6.
  pose (interface_component_id_correspondance P HWP) as lemma.
  specialize (lemma main_cid x).
  assert (In x (interfaceof_P P) /\ get_name x = main_cid).
  Case "Proof of assertion".
  { split. apply H4. apply H6. }
  apply lemma in H8.
  destruct H8.
  apply component_index_correspondance_eq in H8.
  apply component_index_correspondance_in in H8.
  apply H8. apply HWP. apply HWP.
Qed.

Lemma program_invariant_correspondance :
  forall P C, wellformed_whole_program P ->
  (nth C (wfinv_of_P P) (0, 0, 0, [])) = 
  (wfinv_of_C (nth C P (0, 0, [], 0, 0, []))).
Proof.
  intros. unfold wfinv_of_P.
  pose (map_nth wfinv_of_C P (0, 0, [], 0, 0, []) C) as lemma.
  apply lemma.
Qed.

Lemma map_interface_correspondance :
  forall C P,
  (interfaceof_C (nth C P (0, 0, [], 0, 0, []))) =
  (nth C (interfaceof_P P) (0, 0, [])).
Proof.
  intros. unfold interfaceof_P.
  pose (map_nth interfaceof_C P (0, 0, [], 0, 0, []) C) as lemma.
  simpl in lemma. rewrite lemma. reflexivity.
Qed.

Lemma updatevalue_doesnt_change_length :
  forall i i' b,
  length (update_value i i' b) = length b.
Proof.
  intros.
  generalize dependent i; generalize dependent i'.
  induction b.
  { destruct i; destruct i'; reflexivity. }
  { destruct i; destruct i'; try (reflexivity);
    simpl. apply f_equal. apply IHb.
    apply f_equal. apply IHb. }
Qed. 

Lemma update_move_value :
  forall s i i' a, 
  S (length (update_value i i' s)) =
length (update_value i i' (a :: s)).
Proof.
  intros.
  generalize dependent i; generalize dependent i'.
  induction s.
  { intros. rewrite updatevalue_doesnt_change_length.
    rewrite updatevalue_doesnt_change_length.
    simpl. reflexivity. }
  { intros. rewrite updatevalue_doesnt_change_length.
    rewrite updatevalue_doesnt_change_length. 
    simpl. reflexivity. }
Qed.

Lemma length_closed_updatevalue :
  forall s i i', 
  length s = length (update_value i i' s).
Proof.
  intros.
  induction s.
  { destruct i; destruct i'; reflexivity. }
  { simpl. rewrite IHs. rewrite <- update_move_value.
    reflexivity. }
Qed.

Lemma length_closed_updatebuffer :
  forall b0 b C0 i i',
  length (nth b0 C0 []) =
  length (nth b0 (update_buffer b i i' C0) []).
Proof.
  intros.
  generalize dependent b0;
  generalize dependent b;
  generalize dependent i;
  generalize dependent i'.
  induction C0.
  { intros. 
    destruct b0; destruct b; destruct i; destruct i';
    try (reflexivity). }
  { intros.
    destruct b0; destruct b; destruct i; destruct i';
    destruct a; simpl; try (reflexivity); try (apply IHC0);
    apply f_equal; apply length_closed_updatevalue. }
Qed.

Lemma length_closed_updatestate :
  forall C b i i' s C0 b0, let s' := (update_state C b i i' s) in
  (length (nth b0 (nth C0 s []) []) = length (nth b0 (nth C0 s' []) [])).
Proof.
  intros. unfold s'.
  generalize dependent b.
  generalize dependent C.
  generalize dependent C0.
  generalize dependent b0.
  unfold update_state.
  unfold update_component.
  induction s;
  destruct b; destruct C; 
  destruct b0; destruct C0;
  try (reflexivity).
  destruct a.
  { reflexivity. }
  { apply length_closed_updatevalue. }
  destruct a.
  { reflexivity. }
  { reflexivity. }
  simpl. apply (IHs 0 C0 C 0).
  simpl. apply (IHs (S b0) C0 C 0).
  destruct a.
  { reflexivity. }
  { reflexivity. }
  destruct a.
  { reflexivity. }
  { simpl. apply (length_closed_updatebuffer b0 b a i i'). }
  simpl. apply (IHs 0 C0 C (S b)).
  simpl. apply (IHs (S b0) C0 C (S b)).
Qed.

Lemma valuedefined_closed_updatestate :
  forall s C b i i' C0 b0 i0,
    value_defined C0 b0 i0 s = true ->
    value_defined C0 b0 i0 (update_state C b i i' s) = true.
Proof.
  intros s C b i i' C0 b0 i0 Hs.
  set (s' := (update_state C b i i' s)).
  assert (length (nth b0 (nth C0 s []) []) = length (nth b0 (nth C0 s' []) [])) as H.
  { unfold s'. apply (length_closed_updatestate C b i i'). }
  unfold value_defined in *.
  now rewrite<- H.
Qed.

Lemma wellformedstate_closed_updatestate :
  forall G s C b i i',
  wellformed_state G s ->
  wellformed_state G (update_state C b i i' s).
Proof.
  intros G s C b i i' H.
  inversion H as [s0 Hs Hseqs0].
  constructor.
  intros.
  apply valuedefined_closed_updatestate.
  now apply Hs.
Qed.

Lemma initial_program_safety :
  forall P, wellformed_whole_program P ->
  let Is := interfaceof_P P in
  let G := wfinv_of_P P in
  wellformed_cfg Is G (initial_cfg_of P).
Proof.
  simpl. intros p HWP.
  inversion HWP as [p' HI HPP].
  inversion HI. inversion HPP.
  unfold initial_cfg_of. constructor.
  Case "State wellformed".
  { constructor. intros.
    destruct H7. unfold l in H7; unfold l' in H8.
    unfold value_defined.
    assert ((nth b (get_blens n) 0) = 
    (length
       (nth b
          (nth (get_nameN n)
             (update_state main_cid 0 0 0 (generate_state p))
             []) []))) as getblens_is_lengthbuffer.
    SCase "Proof of assertion".
    { destruct n as [[[name bnum] pnum] blens] eqn:HD.
      simpl in H7; simpl in H8.
      simpl (get_blens (name, bnum, pnum, blens)).
      simpl (get_nameN (name, bnum, pnum, blens)).
      assert (length
        (nth b
          (nth name (update_state main_cid 0 0 0 (generate_state p))
            []) []) = 
              length
        (nth b
          (nth name (generate_state p)
            []) [])) as Hassert.
      SSCase "Proof of assertion".
      { pose (length_closed_updatestate main_cid 0 0 0 (generate_state p) name b) as lemma.
        simpl in lemma. simpl. rewrite lemma. reflexivity. }
      rewrite Hassert.
      intros. unfold generate_state. 
      pose (map_nth get_buffers p (0,0,[],0,0,[]) name) as lemma.
      simpl in lemma. rewrite lemma.
      assert (blens = (map (@length nat)
        (get_buffers (nth name p (0, 0, [], 0, 0, []))))).
      SSSCase "Proof of assertion".
      { unfold wfinv_of_P in H6.
        pose (in_map_iff wfinv_of_C p n) as lemma'.
        destruct lemma'. rewrite HD in H9.
        apply H9 in H6. destruct H6. destruct H6 as [HH1 HH2].
        destruct x as [[[[[k1 k2] k3] k4] k5] k6].
        inversion HH1.
        clear HI; clear HPP; clear H0; clear H1; clear H2.
        assert ((get_buffers (nth name p (0, 0, [], 0, 0, []))) = k3) as Hassert'.
        SSSSCase "Proof of assertion".
        { admit.
        }
        rewrite Hassert'. reflexivity.
      }
      rewrite H9.
      pose (@map_nth buffer nat (@length nat) (get_buffers (nth name p (0, 0, [], 0, 0, [])))
        [] b) as lemma'.
      simpl in lemma'. rewrite <- lemma'.
      reflexivity.
    } 
    rewrite <- (getblens_is_lengthbuffer).
    apply andb_true in H8. destruct H8.
    rewrite H8; rewrite H9.
    reflexivity.
  }
  Case "Callstack wellformed".
  { constructor. }
  { destruct H2. destruct H2. destruct H6.
    pose (interface_component_id_correspondance p HWP main_cid x) as lemma.
    assert (In x (interfaceof_P p) /\ get_name x = main_cid) as Hassert.
    split. apply H2. apply H6.
    apply lemma in Hassert. destruct Hassert. destruct H8.
    specialize (H4 main_cid x0). destruct H4. destruct H10.
    apply H4 in H8. inversion H8. specialize (H13 0).
    rewrite H9 in H12.
    apply H12.
  }
  Case "Continuations wellformed".
  { constructor. }
  Case "Expr".
  { destruct H2; destruct H2; destruct H6.
    rewrite program_invariant_correspondance.
    specialize (H4 main_cid (nth main_cid p (0,0,[],0,0,[]))).
    pose (correct_program_contains_main) as lemma.
    destruct H4. destruct H8.
    apply H4 in lemma. inversion lemma.
    specialize (H11 0). simpl in H11.
    pose (interface_component_index_correspondance_eq x p main_cid HWP) as lemma'.
    rewrite lemma' in H11. apply H11.
    apply H7.
    split.
    SCase "Left".
    { apply H2. }
    SCase "Right".
    { apply H6. }
    apply HWP. apply HWP.
  }
Admitted.

Definition partial_progress : Prop :=
  forall P, wellformed_whole_program P ->
  let Is := interfaceof_P P in
  let G := wfinv_of_P P in
  let D := procbodies P in
  forall cfg, wellformed_cfg Is G cfg ->
  (final_cfg cfg \/ undefined_cfg D cfg \/ (exists cfg', D ⊢ cfg ⇒ cfg')).

Definition preservation : Prop :=
  forall P, wellformed_whole_program P ->
  let Is := interfaceof_P P in
  let G := wfinv_of_P P in
  let D := procbodies P in
  forall cfg cfg', 
    (wellformed_cfg Is G cfg ->
     D ⊢ cfg ⇒ cfg' ->
     wellformed_cfg Is G cfg').

Theorem partial_progress_proof:
  partial_progress.
Proof.
  unfold partial_progress.
  intros P WP cfg' WCFG.
  induction WCFG.
  remember (C, s, d, K, e) as cfg. rewrite Heqcfg.
  destruct K as [|f K0]; destruct e; destruct d as [|c0 d0];
  try (destruct f);
  try (destruct (value_defined C b n s) eqn:vdn);
  try (destruct (value_defined C b n0 s) eqn:vdn0);
  (* Eliminate final cfg cases *)
  try (left; now constructor);
  (* Progression cases *)
  try (
    try (destruct n);
    right; right;
    exists (eval_cfg (procbodies P) cfg 1);
    try (destruct c0);
    rewrite Heqcfg; 
    simpl;
    try (rewrite vdn);
    try (rewrite vdn0);
    now constructor
  );
  try (try (destruct n); now reflexivity);
  try (try (destruct f); try (destruct n); unfold not; intro contra; now inversion contra);  
  (* Undefined cfg cases *)
  try (right; left; constructor; unfold value_undefined; try (rewrite vdn); try (rewrite vdn0); now reflexivity).
Qed.

Lemma wf_flatevalcon_implies_expr :
  forall i n E,
  wellformed_expr i n (flatevalcon_to_expr E) -> 
  wellformed_flatevalcon i n E.
Proof.
  intros.
  inversion H.
  constructor.
  apply H0.
  apply H1.
  apply H2.
Qed.

Lemma procbody_correspondance :
  forall p C P, wellformed_whole_program P ->
  (nth p (get_procs (nth C P (0, 0, [], 0, 0, []))) exit)
    = (fetch_context C p (procbodies P)).
Proof.
  intros. unfold fetch_context. unfold procbodies.
  assert ((get_procs (nth C P (0, 0, [], 0, 0, []))) =
    (nth C (map get_procs P) [])) as HA.
  Case "Proof of assertion".
  { pose (map_nth get_procs P (0, 0, [], 0, 0, []) C) as lemma;
    symmetry in lemma. simpl in lemma.
    apply lemma.
  }
  rewrite HA; reflexivity.
Qed.

Theorem preservation_proof :
  preservation.
Proof.
  unfold preservation.
  intros P HWP cfg cfg' HCFG Heval.  
  inversion Heval as [C| | | | | | | | | | | | |]; constructor;
  rename H into H_Eval1; rename H0 into H_Eval2;
  inversion HCFG as [n state cs cont expr HS HC Hdef HK HE];
  try (
    try (rename H into WFD);
    try (rewrite <- WFD in H_Eval1);
    try (rewrite <- WFD in H_Eval2);
    try (inversion H_Eval1);
    try (inversion H_Eval2);
    rename H0 into DC; rename H1 into DS; rename H2 into DD;
    rename H3 into DK; rename H4 into DE
  );
  (* State *)
  try (apply HS);
  (* Callstack *)
  try (apply HC);
  (* Continuations *)
  try (constructor);
  try (constructor);
  try (
    rewrite <- DE in HE;
    inversion HE; 
    try (apply H4); try (apply H2);
    try (destruct H_Eval1);
    try (apply HK)
  );
  try (rewrite <- DK in HK; inversion HK; apply H4);
  try (
    rewrite <- DK in HK;
    inversion HK;
    inversion H3;
    apply H6
  );
  try (
    rewrite <- DK in HK;
    inversion HK;
    inversion H3;
    apply H5
  );
  try (
    destruct op; simpl;
    try (destruct (beq_nat i1 i2));
    try (destruct (ble_nat i1 i2));
    try (now constructor)
  );
  try (now apply H3);
  try (
    rewrite <- DE in HK;
    inversion HK;
    apply H2
  );
  try (
    rewrite <- DE in HK;
    inversion HK;
    inversion H1;
    apply H6
  );
  try (
    rewrite <- DK in HK;
    inversion HK;
    inversion H3;
    apply H8
  );
  try (
    rewrite <- H5 in HK;
    inversion HK;
    inversion H5;
    apply H2
  );
  try (apply HC);
  try (
    rewrite <- DD in HC;
    inversion HC;
    apply H6
  );
  (* Component defined cases *)
  try (apply Hdef);
  try (
    rewrite <- DD; rewrite <- DK;
    rewrite DC; rewrite DD; apply Hdef
  ).
  (* Buffer Checking *)  
  destruct (ble_nat b (get_bnumN (nth n (wfinv_of_P P) (0, 0, 0, []))) &&
    negb (b =? get_bnumN (nth n (wfinv_of_P P) (0, 0, 0, [])))) eqn:HD.
  reflexivity.
  rewrite <- DK in HK.
  inversion HK.
  inversion H3.
  unfold l in H7.
  rewrite HD in H7.
  inversion H7.
  (* State with update *)
  intros.
  rewrite <- WFD in HCFG.
  inversion HCFG.
  inversion H8.
  specialize (H13 n0 H b0 i0).
  apply (valuedefined_closed_updatestate).
  apply H13. apply H0.
  (* State with update *)
  intros.
  rewrite <- WFD in HCFG.
  inversion HCFG.
  inversion H8.
  specialize (H13 n0 H0 b i).
  rewrite <- DS.
  apply (valuedefined_closed_updatestate).
  apply H13. apply H2.
  (* External component defined in expr *)
  rewrite <- DK in HK. inversion HK.
  inversion H3. destruct H6.
  Case "Call In".
  { destruct H6.
    pose (interface_index_correspondance_eq P HWP n) as lemma.
    rewrite lemma in H6. rewrite H6. apply Hdef. apply Hdef.
  }
  Case "Call Out".
  { destruct H6. inversion HWP. inversion H9.
    assert (In (interfaceof_C (nth C P (0,0,[],0,0,[]))) (interfaceof_P P)) as Hassert.
    SCase "Proof of assertion".
    { unfold component_defined in Hdef.
      apply andb_true in Hdef. destruct Hdef as [Hdef1 Hdef2].
      pose (@nth_In interface n (interfaceof_P P) (0, 0, [])) as lemma.
      apply blenat_implies_leq in Hdef1.
      apply lemma in Hdef1. rewrite <- map_interface_correspondance in Hdef1.
      rewrite <- DC in Hdef1. apply Hdef1.
    }
    apply H12 in Hassert.
    inversion Hassert. rewrite <- DC in H8.
    specialize (H18 C' P'). apply H18.
    rewrite <- map_interface_correspondance in H8.
    apply H8.
  }
  (* Expr ep wellformed *)
  unfold ep. inversion HWP. inversion H0.
  destruct H6; destruct H6; destruct H8.
  inversion H2.
  specialize (H10 C' (nth C' P (0,0,[],0,0,[]))).
  assert (In (nth C' P (0, 0, [], 0, 0, [])) P) as Hassert.
  Case "Proof of assertion".
  { rewrite <- DK in HK. inversion HK.
    inversion H14. simpl in H17. destruct H17. destruct H17.
    SCase "Call in".
    { pose (interface_index_correspondance_eq P HWP n) as lemma.
      rewrite lemma in H17. rewrite H17.
      pose (@nth_In interface n (interfaceof_P P) (0, 0, [])) as lemma'.
      assert (Hdef' := Hdef).
      unfold component_defined in Hdef. apply andb_true in Hdef.
      destruct Hdef as [Hdef1 Hdef2].
      apply blenat_implies_leq in Hdef1.
      apply lemma' in Hdef1.
      pose (interface_component_index_correspondance_eq 
        (nth n (interfaceof_P P) (0, 0, [])) P n HWP) as lemma''.
      pose (interface_index_correspondance_eq P HWP n) as lemma'''.
      assert (In (nth n (interfaceof_P P) (0, 0, []))
            (interfaceof_P P) /\
          get_name (nth n (interfaceof_P P) (0, 0, [])) = n) as Hassert.
      SSCase "Proof of assertion".
      { split. apply Hdef1. apply lemma'''. apply Hdef'. }
      apply lemma'' in Hassert.
      apply (component_index_correspondance_in n P HWP).
      apply Hassert. apply Hdef.
    }
    SCase "Call out".
    { assert (In (interfaceof_C (nth C P (0,0,[],0,0,[]))) (interfaceof_P P)) as Hassert.
      SSCase "Proof of assertion".
      { unfold component_defined in Hdef.
        apply andb_true in Hdef. destruct Hdef as [Hdef1 Hdef2].
        pose (@nth_In interface n (interfaceof_P P) (0, 0, [])) as lemma.
        apply blenat_implies_leq in Hdef1.
        apply lemma in Hdef1. rewrite <- map_interface_correspondance in Hdef1.
        rewrite <- DC in Hdef1. apply Hdef1.
      }
      apply H4 in Hassert.
      inversion Hassert.
      destruct H17. specialize (H21 C' P').
      rewrite <- DC in H23.
      rewrite <- map_interface_correspondance in H23.
      assert (H23' := H23).
      apply H21 in H23.
      unfold component_defined in H23. destruct H23.
      apply andb_true in H24. destruct H24 as [Hdef2 Hdef2'].
      pose (@nth_In interface C' (interfaceof_P P) (0, 0, [])) as lemma.
      apply blenat_implies_leq in Hdef2.
      apply lemma in Hdef2. rewrite <- map_interface_correspondance in Hdef2.
      pose (interface_component_index_correspondance_eq 
        (nth C' (interfaceof_P P) (0, 0, [])) P C' HWP) as lemma''.
      pose (interface_index_correspondance_eq P HWP C') as lemma'''.
      assert (In (nth C' (interfaceof_P P) (0, 0, []))
            (interfaceof_P P) /\
          get_name (nth C' (interfaceof_P P) (0, 0, [])) = C') as Hassert'.
      SSCase "Proof of assertion".
      { split. rewrite <- map_interface_correspondance.
        apply Hdef2. apply lemma'''. apply H21. apply H23'. 
      }
      apply lemma'' in Hassert'.
      apply (component_index_correspondance_in C' P HWP).
      apply Hassert'.
    }
  }
  assert (Hassert2 := Hassert). destruct H10.
  apply H10 in Hassert.
  inversion Hassert.
  simpl in H12. specialize (H14 P').
  rewrite program_invariant_correspondance.
  assert ((get_nameC (nth C' P (0, 0, [], 0, 0, []))) = C') as Hassert'.
  Case "Proof of assertion".
  { apply (component_index_correspondance_eq' C' P HWP Hassert2). }
  rewrite Hassert' in H12. 
  unfold procbodies. unfold fetch_context.
  assert (get_procs (nth C' P (0, 0, [], 0, 0, []))
    = nth C' (map get_procs P) []) as Hassert''.
  Case "Proof of assertion".
  { unfold procbodies. unfold fetch_context.
    pose (map_nth get_procs P (0, 0, [], 0, 0, []) C') as lemma.
    simpl in lemma. symmetry in lemma. apply lemma.
  }
  rewrite <- Hassert''. simpl in H14.
  rewrite Hassert' in H14. apply H14.
  inversion H0.
  specialize (H18 (nth C (interfaceof_P P) (0,0,[]))).
  rewrite <- map_interface_correspondance in H18.
  rewrite <- DK in HK. inversion HK. inversion H24.
  destruct H27.
  Case "Call In".
  { destruct H27. unfold procedure_defined_interfaces.
    destruct H29. apply andb_true in H30. destruct H30.
    rewrite H27. pose (interface_index_correspondance_eq P HWP n) as lemma.
    rewrite lemma. rewrite H30. rewrite H31. simpl. reflexivity.
    apply Hdef.
  }
  Case "Call Out".
  { simpl in H27. destruct H27. rewrite <- DC in H29.
    assert (In (interfaceof_C (nth C P (0, 0, [], 0, 0, [])))
        (interfaceof_P P)).
    SCase "Proof of assertion".
    { rewrite <- DC in Hdef.
      pose (interface_index_correspondance_eq P HWP C) as lemma.
      apply lemma in Hdef. inversion H2. unfold interfaceof_P in Hdef.
      pose (map_nth interfaceof_C P (0, 0, [], 0, 0, []) C) as lemma'.
      simpl in lemma'. rewrite lemma' in Hdef.
      rewrite <- interfacename_is_componentname in Hdef.
      specialize (H30 C (nth C P (0, 0, [], 0, 0, []))).
      destruct H30. destruct H32. destruct H33.
      apply H34 in Hdef.
      pose (in_map interfaceof_C P (nth C P (0, 0, [], 0, 0, []))) as lemma''.
      apply lemma'' in Hdef. unfold interfaceof_P. apply Hdef.
    }
    apply H18 in H30. inversion H30.
    specialize (H33 C' P'). unfold interfaceof_P in H29.
    pose (map_nth interfaceof_C P (0, 0, [], 0, 0, []) C) as lemma.
    simpl in lemma. rewrite lemma in H29. apply H33 in H29.
    destruct H29. apply H29.
  }
  apply HWP.
  (* State with update *)
  intros.
  rewrite <- WFD in HCFG.
  inversion HCFG.
  inversion H8.
  specialize (H13 n0 H0 b i0).
  apply (valuedefined_closed_updatestate).
  rewrite <- DS.
  apply H13. apply H2.
  (* Empty continuation *)
  rewrite <- DD in HC.
  inversion HC.
  apply H7.
  (* External component defined in call *)
  rewrite <- WFD in HCFG.
  inversion HCFG. inversion H7.
  apply H14.
Qed.

Theorem partial_type_safety :
  partial_progress /\ preservation.
Proof.
  split.
  apply partial_progress_proof; assumption.
  apply preservation_proof.
Qed.

(* _____________________________________ 
             CLASSIC PROOFS
   _____________________________________ *)

(* ---- Computational/Relational evaluation equivalence ---- *)

Lemma eval_cfg_1step : 
  forall (D:context) (c : cfg),
  (final_cfg c \/ undefined_cfg D c \/ D ⊢ c ⇒ eval_cfg D c 1).
Proof.
  intros.
  destruct c as [[[[C s] d] K] e].
  destruct e;
  destruct d as [|call d'];
  destruct K as [|k K'];
  try (left; constructor);
  try (destruct k);
  try (destruct call);
  try (try (destruct n); right; right; constructor);
  try (intro contra; inversion contra);
  try reflexivity; simpl;
  try (destruct (value_defined C b n s) eqn:HD1);
  try (destruct (value_defined C b n0 s) eqn:HD2);
  try (try (destruct n); right; right; constructor);
  try (apply HD1); try (apply HD2);
  try (
    right; left; constructor; 
    unfold value_undefined; 
    try (rewrite HD1); try (rewrite HD2); now reflexivity
  ).
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
      destruct H.
      SCase "undefined".
          inversion H;
          destruct d; try (destruct c0); simpl; 
          apply negation_transfert in H0; simpl in H0;
          rewrite H0; simpl;
          apply IHi'.
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
  );
  try (simpl; rewrite H; rewrite H0; simpl; reflexivity).
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

(* ---- Determinism of small-step evaluation ---- *)

Theorem smallstep_deterministic :
  forall D, deterministic (small_step D).
Proof.
  unfold deterministic.
  intros D c a b H0 H1.
  pose (smallstep_eval_1step D c a H0) as H0'.
  pose (smallstep_eval_1step D c b H1) as H1'.
  rewrite <- H0'. rewrite <- H1'. reflexivity.
Qed.

(* ---- partial_progress_context ---- *)

Theorem partial_progress_context :
  forall c D, 
  undefined_cfg D c \/ final_cfg c \/ exists c', D ⊢ c ⇒ c'.
Proof.
  intros. 
  pose (eval_cfg_1step D c) as lemma.
  destruct lemma.
  Case "final".
    right. left. apply H.
  destruct H.
  Case "undefined".
    left. apply H.
  Case "evaluable".
    right. right. exists (eval_cfg D c 1).
    apply H.
Qed.

(* ---- Normal forms ---- *)

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Theorem finalcfg_normalform_equivalence :
  forall c D, (final_cfg c \/ undefined_cfg D c)
  <-> normal_form (small_step D) c.
Proof.
  intros. split.
  Case "->".
  { intro H. unfold normal_form.
    destruct H. inversion H.
    SCase "final value".
      intro contra. destruct contra.
      inversion H1.
    SCase "final exit".
      intro contra. destruct contra.
      inversion H1.
    SCase "undefined".
      intro contra. destruct contra;
      try (inversion H);
      rewrite <- H3 in H0; inversion H0;
      unfold value_undefined in H1;
      try (rewrite H11 in H1);
      try (rewrite H12 in H1); 
      inversion H1.
  }
  Case "<-".
  { intro H. unfold normal_form in H.
    unfold not in H.
    assert (undefined_cfg D c \/ final_cfg c \/ 
           (exists c' : cfg, D ⊢ c ⇒ c')).
      apply partial_progress_context.
    destruct H0.
    SCase "undefined".
      right. apply H0.  
    destruct H0.
    SCase "final".
      left. apply H0.
    SCase "evaluable".
      apply H in H0.
      contradiction.
  }
Qed.
