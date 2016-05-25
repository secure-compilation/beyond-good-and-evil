Require Import Target.

(* _____________________________________ 
                  SYNTAX
   _____________________________________ *)

Inductive origin : Type :=
  | ContextOrigin : origin
  | ProgramOrigin : origin.

Inductive external_action : Type :=
  | ExtCall : component_id -> procedure_id -> registers -> 
    external_action
  | ExtRet : registers -> external_action
  | End : external_action.

Inductive internal_action : Type :=
  | IntTau : internal_action
  | IntCall : component_id -> procedure_id -> internal_action
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

Definition sigma :=
  list (component_id * nat).

Definition A_sigma :=
  list (component_id).

Inductive alt_list (A B : Type) : Type :=
  | alt_init : A -> alt_list A B
  | alt_cons : A -> alt_list B A -> alt_list A B.

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
   A_SIGMA *
   global_memory).

Inductive state_partial_view : Type :=
  | ProgramControl : program_state -> state_partial_view
  | ContextControl : context_state -> state_partial_view
  | EXITED.

(* ------- Definitions : Extra notations ------- *)

Definition Top {A B : Type} (E:alt_list A B) : A :=
  match E with
  | alt_init _ _ h => h 
  | alt_cons _ _ h t => h
  end.

Definition SetTop {A B : Type} (E:alt_list A B) (new:A)
  : alt_list A B :=
  match E with
  | alt_init _ _ h => alt_init A B new
  | alt_cons _ _ h t => alt_cons A B new t 
  end.


(* _____________________________________ 
                REDUCTIONS
   _____________________________________ *)

Inductive reduction (Is:program_interfaces) (E:entry_points) : 
  state_partial_view -> state_partial_view -> trace -> Prop :=
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
    (Top PE = o) -> (PE' = SetTop PE o') ->
    step Is E (C,d,mem,reg,pc) (C',d',mem',reg',pc') ->
    reduction Is E 
      (ProgramControl (C,PE,mem,reg,pc)) 
      (ProgramControl (C',PE',mem',reg',pc'))
      [action (C,d,mem,reg,pc)]
  | T_TauMinus : forall C AE mem,
    reduction Is E 
      (ContextControl (C, AE, mem)) 
      (ContextControl (C, AE, mem)) 
      [Int IntTau ContextOrigin]
  | T_CallMinus : forall C C' P' AE AE' Ao mem,
    (component_defined C interface Is = true) ->
    In (C', P') (get_import (nth C Is (0,0,[]))) \/ (C' = C) ->
    ~(In C' (dom_entry_points E)) -> (Top AE = Ao) ->
    (AE' = SetTop AE (C::Ao)) ->
    reduction Is E 
      (ContextControl (C, AE, mem))
      (ContextControl (C', AE',mem)) 
      [Int (IntCall C' P') ContextOrigin]
  | T_RetMinus : forall C C' AE AE' o mem,
    (C'::o = Top AE) -> (AE' = SetTop AE o) ->
    reduction Is E
      (ContextControl (C, AE, mem))
      (ContextControl (C', AE', mem))
      [Int IntRet ContextOrigin]
  | T_CallCtx : forall C C' P' AE AE' Ao reg mem,
    (component_defined C interface Is = true) ->
    In (C',P') (get_import (nth C Is (0,0,[]))) ->
    (In C' (dom_entry_points E)) -> (Top AE = Ao) ->
    (AE' = SetTop AE (C::Ao)) ->
    reduction Is E 
    (ContextControl (C,AE,mem))
    (ProgramControl (C',(alt_cons sigma A_sigma [] AE'),
      mem,reg,fetch_entry_points C' P' E))
        [Ext (ExtCall C' P' reg) ContextOrigin]
  | T_RetCtx : forall C C' pc o PE PE' reg mem,
    (Top PE = (C',pc)::o) -> (PE' = SetTop PE o) ->
    reduction Is E 
    (ContextControl (C, (alt_cons A_sigma sigma [] PE), mem))
    (ProgramControl (C',PE',mem,reg,pc))
      [Ext (ExtRet reg) ContextOrigin]
  | T_CallPrg : forall C C' P' o PE PE' mem reg pc i,
    (fetch_mem C mem pc = i) -> (decode i = Some (Call C' P')) ->
    (component_defined C interface Is = true) ->
    (In (C',P') (get_import (nth C Is (0,0,[])))) ->
    ~(In C' (dom_entry_points E)) -> (Top PE = o) ->
    (PE' = SetTop PE ((C,pc+1)::o)) ->
    reduction Is E
    (ProgramControl (C,PE,mem,reg,pc))
    (ContextControl (C',(alt_cons A_sigma sigma [] PE'),mem))
      [Ext (ExtCall C' P' reg) ProgramOrigin]
  | T_RetPrg : forall C C' Ao AE AE' i pc mem reg,
    (fetch_mem C mem pc = i) -> (decode i = Some Return) ->
    (Top AE = C'::Ao) -> (AE' = SetTop AE Ao) ->
    reduction Is E 
    (ProgramControl (C,(alt_cons sigma A_sigma [] AE),mem,reg,pc))
    (ContextControl (C',AE',mem))
      [Ext (ExtRet reg) ProgramOrigin]
  | T_ExitCtx : forall C AE mem,
    reduction Is E
    (ContextControl (C,AE,mem)) EXITED [Ext End ContextOrigin]
  | T_ExitPrg : forall theta C PE mem reg pc,
    (forall alpha, (alpha <> (Ext End ProgramOrigin) ->
      reduction Is E (ProgramControl(C,PE,mem,reg,pc)) theta [alpha])) ->
    reduction Is E
    (ProgramControl (C,PE,mem,reg,pc)) EXITED [Ext End ProgramOrigin].





