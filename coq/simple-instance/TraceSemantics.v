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
  state_partial_view -> state_partial_view -> action -> Prop :=
  (* T_CallRetTau+ *)
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
      (action (C,d,mem,reg,pc))
  (* T_TauMinus- *)
  | T_TauMinus : forall C AE mem,
    reduction Is E 
      (ContextControl (C, AE, mem)) 
      (ContextControl (C, AE, mem)) 
      (Int IntTau ContextOrigin)
  (* T_Call- *)
  | T_CallMinus : forall C C' P' AE AE' Ao mem,
    (component_defined C interface Is = true) ->
    In (C', P') (get_import (nth C Is (0,0,[]))) \/ (C' = C) ->
    ~(In C' (dom_entry_points E)) -> (Top AE = Ao) ->
    (AE' = SetTop AE (C::Ao)) ->
    reduction Is E 
      (ContextControl (C, AE, mem))
      (ContextControl (C', AE',mem)) 
      (Int (IntCall C' P') ContextOrigin)
  (* T_Ret- *)
  | T_RetMinus : forall C C' AE AE' o mem,
    (C'::o = Top AE) -> (AE' = SetTop AE o) ->
    reduction Is E
      (ContextControl (C, AE, mem))
      (ContextControl (C', AE', mem))
      (Int IntRet ContextOrigin)
  (* T_Call? *)
  | T_CallCtx : forall C C' P' AE AE' Ao reg mem,
    (component_defined C interface Is = true) ->
    In (C',P') (get_import (nth C Is (0,0,[]))) ->
    (In C' (dom_entry_points E)) -> (Top AE = Ao) ->
    (AE' = SetTop AE (C::Ao)) ->
    reduction Is E 
    (ContextControl (C,AE,mem))
    (ProgramControl (C',(alt_cons sigma A_sigma [] AE'),
      mem,reg,fetch_entry_points C' P' E))
        (Ext (ExtCall C' P' reg) ContextOrigin)
  (* T_Ret? *)
  | T_RetCtx : forall C C' pc o PE PE' reg mem,
    (Top PE = (C',pc)::o) -> (PE' = SetTop PE o) ->
    reduction Is E 
    (ContextControl (C, (alt_cons A_sigma sigma [] PE), mem))
    (ProgramControl (C',PE',mem,reg,pc))
      (Ext (ExtRet reg) ContextOrigin)
  (* T_Call! *)
  | T_CallPrg : forall C C' P' o PE PE' mem reg pc i,
    (fetch_mem C mem pc = i) -> (decode i = Some (Call C' P')) ->
    (component_defined C interface Is = true) ->
    (In (C',P') (get_import (nth C Is (0,0,[])))) ->
    ~(In C' (dom_entry_points E)) -> (Top PE = o) ->
    (PE' = SetTop PE ((C,pc+1)::o)) ->
    reduction Is E
    (ProgramControl (C,PE,mem,reg,pc))
    (ContextControl (C',(alt_cons A_sigma sigma [] PE'),mem))
      (Ext (ExtCall C' P' reg) ProgramOrigin)
  (* T_Ret! *)
  | T_RetPrg : forall C C' Ao AE AE' i pc mem reg,
    (fetch_mem C mem pc = i) -> (decode i = Some Return) ->
    (Top AE = C'::Ao) -> (AE' = SetTop AE Ao) ->
    reduction Is E 
    (ProgramControl (C,(alt_cons sigma A_sigma [] AE),mem,reg,pc))
    (ContextControl (C',AE',mem))
      (Ext (ExtRet reg) ProgramOrigin)
  (* T_Exit? *)
  | T_ExitCtx : forall C AE mem,
    reduction Is E
    (ContextControl (C,AE,mem)) EXITED (Ext End ContextOrigin)
  (* T_Exit! *)
  | T_ExitPrg : forall theta C PE mem reg pc,
    (forall alpha, (alpha <> (Ext End ProgramOrigin) ->
      reduction Is E (ProgramControl(C,PE,mem,reg,pc)) theta alpha)) ->
    reduction Is E
    (ProgramControl (C,PE,mem,reg,pc)) EXITED (Ext End ProgramOrigin).


(* _____________________________________ 
          INITIAL TRACE STATES
   _____________________________________ *)

Definition initial_trace_state (P:Target.program) : 
  state_partial_view :=
  match P with
  | (Is, mem, E) =>
    let CS_PRG := (alt_init sigma A_sigma []) in
    let CS_CTX := (alt_init A_sigma sigma []) in
    if existsb (fun x => main_cid =? x) (dom_entry_points E) then
      ProgramControl (main_cid, CS_PRG, mem, g_regs, 
        fetch_entry_points main_cid 0 E)
    else
      ContextControl (main_cid, CS_CTX, mem)
  end.


(* _____________________________________ 
            TRACE DUALIZATION
   _____________________________________ *)

Definition dual_trace (t:trace) :=
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
            ACTION COMPOSITION
   _____________________________________ *)

Inductive reduction_multi (Is:program_interfaces) (E:entry_points) :
  state_partial_view -> state_partial_view -> trace -> Prop :=
  (* T_Refl *)
  | T_Refl : forall o o', 
    reduction_multi Is E o o' []
  (* T_Internal *)
  | T_Internal : forall o o' Ia origin,
    reduction Is E o o' (Int Ia origin) ->
    reduction_multi Is E o o' []
  (* T_Cross *)
  | T_Cross : forall o o' Ea origin,
    reduction Is E o o' (Ext Ea origin) ->
    reduction_multi Is E o o' [Ext Ea origin]
  (* T_Trans *)
  | T_Trans : forall o o' o'' t u,
    reduction Is E o o' t ->
    reduction Is E o' o'' u ->
    reduction_multi Is E o o'' ([t]++[u]).


(* _____________________________________ 
       INFERENCE RULES FOR CONTEXT
   _____________________________________ *)

Inductive reduction_duality (Is:program_interfaces) (E:entry_points) :
  state_partial_view -> state_partial_view -> trace -> Prop := 
  | T_Dual : forall o o' t,
    reduction_multi Is E o o' (dual_trace t) ->
    reduction_duality Is E o o' t.


(* _____________________________________ 
       TRACES WITH INTERNAL ACTIONS
   _____________________________________ *)

Fixpoint erase (t:trace) : trace :=
  match t with
  | [] => []
  | (Int _ _)::t => erase t
  | (Ext Ea origin)::t =>
    (Ext Ea origin) :: (erase t)
  end.


(* _____________________________________ 
         TRACE CANONICALIZATION
   _____________________________________ *)

Definition zeta_gamma (Ea:external_action) : external_action :=
  match Ea with
  | ExtCall C P reg => ExtCall C P (clear_regs reg)
  | ExtRet reg => ExtRet (clear_regs reg) 
  | End => End
  end.

Definition zetaC_Ea (a:action) : action :=
  match a with
  | Ext gamma ContextOrigin => Ext (zeta_gamma gamma) ContextOrigin
  | _ => a
  end.

Fixpoint zetaC_t (t:trace) : trace :=
  match t with
  | [] => []
  | (Ext g ContextOrigin)::t' => 
    (zetaC_Ea (Ext g ContextOrigin))::(zetaC_t t')
  | _ => t
  end.

Fixpoint zetaC_T (T:trace) : trace :=
  match T with
  | [] => []
  | (Ext g ContextOrigin)::T' => (zetaC_Ea (Ext g ContextOrigin))::(zetaC_T T')
  | (Int g ContextOrigin)::T' => (Int g ContextOrigin)::(zetaC_T T')
  | _ => T
  end.

Definition zetaP_Ea (a:action) : action :=
  match a with
  | Ext gamma ProgramOrigin => Ext (zeta_gamma gamma) ProgramOrigin
  | _ => a
  end.

Fixpoint zetaP_t (t:trace) : trace :=
  match t with
  | [] => []
  | (Ext g ProgramOrigin)::t' => 
    (zetaP_Ea (Ext g ProgramOrigin))::(zetaP_t t')
  | _ => t
  end.

Fixpoint zetaP_T (T:trace) : trace :=
  match T with
  | [] => []
  | (Ext g ProgramOrigin)::T' => 
    (zetaP_Ea (Ext g ProgramOrigin))::(zetaP_T T')
  | (Int g ProgramOrigin)::T' => 
    (Int g ProgramOrigin)::(zetaP_T T')
  | _ => T
  end.


(* _____________________________________ 
            WELL-FORMEDNESS
   _____________________________________ *)

Inductive wellformed_o (E:entry_points) : sigma -> Prop :=
  | WF_Nil_o :
    wellformed_o E []
  | WF_Cons_o : forall o o' C pc,
    (o = (C,pc)::o') -> (In C (dom_entry_points E)) ->
    (wellformed_o E o') -> (wellformed_o E o).

Inductive wellformed_Ao (E:entry_points) : A_sigma -> Prop :=
  | WF_Nil_Ao :
    wellformed_Ao E []
  | WF_Cons_Ao : forall C Ao Ao',
    (Ao = C::Ao') -> ~(In C (dom_entry_points E)) ->
    (wellformed_Ao E Ao') -> (wellformed_Ao E Ao).

Inductive wellformed_PE (E:entry_points) : P_SIGMA -> Prop :=
  | WF_Init_PE : forall o PE,
    PE = alt_init sigma A_sigma o -> wellformed_PE E PE
  | WF_Cons_PE : forall PE AE h t o,
    PE = alt_cons sigma A_sigma o AE ->
    Top AE = h::t ->
    wellformed_o E o -> wellformed_AE E AE ->
    wellformed_PE E PE
with wellformed_AE (E:entry_points) : A_SIGMA -> Prop :=
  | WF_Init_AE : forall AE Ao,
    AE = alt_init A_sigma sigma Ao -> wellformed_AE E AE
  | WF_Cons_AE : forall AE Ao h t PE,
    AE = alt_cons A_sigma sigma Ao PE ->
    Top PE = h::t ->
    wellformed_Ao E Ao -> wellformed_PE E PE ->
    wellformed_AE E AE.

Inductive wellformed_P0 (E:entry_points) : 
  program_state -> Prop :=
  | WF_P0 : forall P0 PE C mem reg pc,
    In C (dom_entry_points E) ->
    (dom_global_memory mem = dom_entry_points E) -> 
    wellformed_PE E PE -> P0 = (C, PE, mem, reg, pc) ->
    wellformed_P0 E P0.

Inductive wellformed_A0 (E:entry_points) :
  context_state -> Prop :=
  | WF_A0 : forall A0 AE C mem,
    ~(In C (dom_entry_points E)) ->
    (dom_global_memory mem = dom_entry_points E) ->
    wellformed_AE E AE -> A0 = (C, AE, mem) ->
    wellformed_A0 E A0.

(* _____________________________________ 
              STATE MERGING
   _____________________________________ *)

Inductive mergeable_Ao_o : A_sigma -> sigma -> Prop :=
  | M_Ao_o_Nil :
    mergeable_Ao_o [] []
  | M_Ao_o_Cons : forall C Ao o i,
    (mergeable_Ao_o Ao o) ->
    mergeable_Ao_o (C::Ao) ((C,i)::o).

Inductive mergeable_PE_AE : P_SIGMA -> A_SIGMA -> Prop :=
  | M_AEPE_Init : forall Ao o,
    mergeable_Ao_o Ao o -> mergeable_PE_AE 
      (alt_init sigma A_sigma o) (alt_init A_sigma sigma Ao)
  | M_AEPE_Cons : forall Ao o AE PE,
    mergeable_Ao_o Ao o -> mergeable_PE_AE PE AE -> mergeable_PE_AE 
    (alt_cons sigma A_sigma o AE) (alt_cons A_sigma sigma Ao PE).

Fixpoint combine_alt {A B C: Type} (f: A -> B -> list C) 
  (e1: alt_list A B) (e2: alt_list B A) :=
  match e1, e2 with
  | alt_init _ _ h1, alt_init _ _ h2 => f h1 h2
  | alt_cons _ _ h1 t1, alt_cons _ _ h2 t2 => 
    f h1 h2 ++ @combine_alt B A C (fun b a => f a b) t1 t2
  | _, _ => []
  end.

(* Assuming they are mergeable *)
Definition merge (e1: P_SIGMA) (e2: A_SIGMA): sigma :=
  combine_alt (fun (s:sigma) (a_s:A_sigma) => s) e1 e2.

Definition option_pair_match
  (p:option component_id * option component_id) : bool :=
  match p with
  | (None, None) => true
  | (Some _, Some _) => true
  | _ => false
  end.

Definition comps_compatible 
  (cs1 cs2 : list (option component_id)) : bool :=
  fold_right andb true (map option_pair_match (combine cs1 cs2)).

(*
Inductive mergeable_P0_A0 : program_state -> context_state -> Prop :=
  | M_P0_A0 : forall PE AE C mem_p mem_A pc reg,
    mergeable_PE_AE PE AE -> dom(memₚ) ∩ dom(memₐ) = ∅ ->
    mergeable_P0_A0 (C,PE,mem_p,reg,pc) (C,AE,mem_a).
*)


(* _____________________________________ 
                PROPERTIES
   _____________________________________ *)










