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
    let blens := map (@length nat) (get_buffers k) in 
    if ble_nat b' bnum then
      (BUFADDR k b') + ((nth b') blens 0)
    else
      0 (*???*)
  end.

(* _____________________________________ 
                MACROS
   _____________________________________ *)

(* _____________________________________ 
         EXPRESSION COMPILATION
   _____________________________________ *)

(*
--------------------------------------
The concrete memory layout is given below:

BUFADDR(κ,0) = 0
BUFADDR(κ,b) when b < κ.bnum = BUFADDR(κ,b-1) + κ.blens[b-1]

EXTERNALENTRY(κ,0) = BUFADDR(κ, κ.bnum-1) + κ.blens[κ.bnum-1]
EXTERNALENTRY(κ,P) when P < κ.pnum = EXTERNALENTRY(κ,P-1) + length(code)
  where code = ((κ.name).(P-1) ↦ κ.procs[P - 1])↓

INTERNALENTRY(κ,P) when P < κ.pnum = EXTERNALENTRY(κ,P) + 3

STACKBASE(κ) = EXTERNALENTRY(κ,κ.pnum - 1) + length(code) + 1
  where code = ((κ.name).(κ.pnum-1) ↦ κ.procs[κ.pnum - 1])↓

The memory cell at location STACKBASE(κ) - 1 is used to (re)store the
stack pointer when switching components.
*)

Fixpoint EXTERNALENTRY (k:component) (P:procedure_id) :=
  match P with
  | 0 => 
    let bnum := (get_bnum k) in
    let blens := map (@length nat) (get_buffers k) in 
    (BUFADDR k (pred bnum)) + (nth (pred bnum) blens 0)
  | S P' => 
    let code := admit in code (* UNCOMPLETED *)
  end.

Definition INTERNALENTRY (k:component) (P:procedure_id) : 
  address := 
  (EXTERNALENTRY k P) + 3.
