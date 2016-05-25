Require Import Target.

(* _____________________________________ 
                  SYNTAX
   _____________________________________ *)

Inductive origin : Type :=
  | ContextOrigin : origin
  | ProgramOrigin : origin.

Inductive external_action : Type :=
  | ExtCall : component_id -> procedure_id -> register -> 
    external_action
  | ExtRet : register -> external_action
  | End : external_action.

Inductive internal_action : Type :=
  | IntTau : internal_action
  | IntCall : component_id -> procedure_id ->
    internal_action
  | IntRet : internal_action.

Inductive action : Type :=
  | Ext : external_action -> origin -> action
  | Int : internal_action -> origin -> action.

Definition trace : Type := list action.

Definition dual (t:trace) :=
  let f :=
    (fun alpha =>
     match alpha with
     | Int ia ProgramOrigin => Int ia ContextOrigin
     | Int ia ContextOrigin => Int ia ProgramOrigin
     | Ext ea ProgramOrigin => Ext ea ContextOrigin
     | Ext ea ContextOrigin => Ext ea ProgramOrigin
     end) in
  map f t.


(* _____________________________________ 
                  STATES
   _____________________________________ *)

Inductive slash : Type := Slash.

Definition sigma :=
  call_stack.

Definition A_sigma :=
  list (component_id * slash).

Inductive alt_list (a b: Type): Type :=
  | init : a -> alt_list a b
  | cons : a -> alt_list b a -> alt_list a b.

Definition A_SIGMA : Type :=
  alt_list A_sigma sigma.

Definition P_SIGMA : Type :=
  alt_list sigma A_sigma.

Definition program_state : Type :=
  (component_id *
   P_SIGMA *
   global_memory *
   registers *
   address).

Definition context_state : Type :=
  (component_id *
   P_SIGMA *
   global_memory).

Inductive state_partial_view : Type :=
  | ProgramControl : Target.state -> state_partial_view
  | ContextControl : Target.state -> state_partial_view
  | EXITED.

(* ------- Definitions : Extra notations ------- *)

Definition Top_PSIGMA (PE:P_SIGMA) : sigma :=
  admit.

Definition Top_ASIGMA (AE:A_SIGMA) : sigma :=
  admit.

Definition SetTop_PSIGMA (PE:P_SIGMA) (o:sigma) : P_SIGMA :=
  admit.

Definition SetTop_ASIGMA (AE:A_SIGMA) (Ao:A_sigma) : A_SIGMA :=
  admit.


(* _____________________________________ 
                REDUCTIONS
   _____________________________________ *)

Inductive reduction (Is:program_interfaces) (E:entry_points) : 
  program_state -> program_state -> action -> Prop :=
  | T_CallRetTauPlus :
    forall C C' d d' mem mem' reg reg' pc pc' o o' PE PE',
    let action := fun cfg =>
      match cfg with
      | (C,d,mem,reg,pc) =>
        match decode (fetch_mem C mem pc) with
        | Some (Call C0 P0) => Int (IntCall C0 P0) ProgramOrigin
        | Some Return => Int IntRet ProgramOrigin 
        | _ => Int IntTau ProgramOrigin
        end
      end
    in 
    Top_PSIGMA = o -> PE' = SetTop_PSIGMA PE o' ->
    step Is E (C,d,mem,reg,pc) (C',d',mem',reg',pc') ->
    reduction Is E (C,PE,mem,reg,pc) (C',PE',mem',reg',pc')
    (action (C,d,mem,reg,pc)). 



