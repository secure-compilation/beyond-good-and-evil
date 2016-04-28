Require Export Source.

(* _____________________________________ 
                  SYNTAX  
   _____________________________________ *)

Definition memory : Type := list nat.

Definition register : Type := nat.

Definition registers : Type := list register.

Inductive binop : Type :=
  | EAdd
  | EMinus
  | EMul.

Inductive instr : Type :=
  | Nop : instr
  | Const : nat -> register -> instr
  | Mov : register -> register -> instr
  | BinOp : binop -> register -> register -> register -> instr
  | Load : register -> register -> instr
  | Store : register -> register -> instr
  | Jal : register -> instr
  | Jump : register -> instr
  | Call : component -> procedure -> instr
  | Return : instr
  | Bnz : register -> nat -> instr
  | Halt : instr.
