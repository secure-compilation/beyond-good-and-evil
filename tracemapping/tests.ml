open OUnit2
open QCheck
open Arbitrary
open Traces
open Semantics
open Mapping

let string_of_alpha alpha =
  match alpha with
  | Int (IntTau, Prg) -> "τ+"
  | Int (IntTau, Ctx) -> "τ-"
  | Int (IntCall (c, p), Prg) -> (string_of_int c) ^ "." ^ (string_of_int p) ^ "(/)+"
  | Int (IntCall (c, p), Ctx) -> (string_of_int c) ^ "." ^ (string_of_int p) ^ "(/)-"
  | Int (IntRet, Prg) -> "Ret/+"
  | Int (IntRet, Ctx) -> "Ret/-"
  | Ext (ExtCall (c, p, i), Prg) -> (string_of_int c) ^ "." ^ (string_of_int p) ^ "(" ^ (string_of_int i) ^ ")!"
  | Ext (ExtCall (c, p, i), Ctx) -> (string_of_int c) ^ "." ^ (string_of_int p) ^ "(" ^ (string_of_int i) ^ ")?"
  | Ext (ExtRet i, Prg) -> "Ret" ^ (string_of_int i) ^ "!"
  | Ext (ExtRet i, Ctx) -> "Ret" ^ (string_of_int i) ^ "?"
  | Ext (Term, Prg) -> "✓!"
  | Ext (Term, Ctx) -> "✓?"

let string_of_trace t =
  let s = ref "" in
  List.iter (fun alpha -> s := !s ^ string_of_alpha alpha ^ "\n") t;
  !s

let string_of_expr e0 =
  let symbols = [(Eq, " = "); (Seq, "; "); (Add, " + ")] in
  let rec aux e =
    match e with
    | EVal v -> string_of_int v
    | EOp (e1, op, e2) ->
       "(" ^ aux e1 ^ ")" ^ (List.assoc op symbols) ^ "(" ^ aux e2 ^ ")"
    | EIfThenElse (e1, e2, e3) ->
       "if { " ^ aux e1 ^ " } then { " ^ aux e2 ^ " } else { " ^ aux e3 ^ " }"
    | ELoad (b, e1) ->
       string_of_int b ^ "[" ^ aux e1 ^ "]"
    | EStore (b, e1, e2) ->
       string_of_int b ^ "[" ^ aux e1 ^ "] := " ^ aux e2
    | ECall (c, p, e1) ->
       string_of_int c ^ "." ^ string_of_int p ^ "(" ^ aux e1 ^ ")"
    | EExit ->
      "exit"
  in
  aux e0

let string_of_component c =
  let s = ref ("component " ^ string_of_int c.name ^ " {\n") in
  Array.iter (fun e -> s := !s ^ "> " ^ string_of_expr e ^ "\n") c.procs;
  !s ^ "}\n"

let string_of_program prg =
  let s = ref "" in
  List.iter (fun c -> s := !s ^ string_of_component c ^ "\n") prg;
  !s

let test (is, t, alpha) _ =
  match alpha with
  | Ext (prg_a, Prg) ->
     let att = build_attacker is t prg_a in
     let t' =
       if prg_a <> Term then
	 dual t @ [Ext (prg_a, Ctx); Ext (Term, Prg)]
       else
	 dual t @ [Ext (prg_a, Ctx)]
     in
     let test_prefix p =
       let expl =
	 "Program A generated for trace t has failed to have prefix p⁻¹ of trace (t.γ₀!.✓?)⁻¹." ^
	 "t⁻¹ =\n" ^ (string_of_trace t') ^
	 "\np⁻¹ =\n" ^ (string_of_trace p) ^
	 "\nA = " ^ (string_of_program att)
       in
       assert_bool expl (has_trace att p)
     in
     let prefixes l =
       List.rev (List.fold_left (fun acc itt -> ((List.hd acc)@[itt])::acc) [[]] l)
     in
     List.iter test_prefix (prefixes t')
  | _ ->
     failwith "dead code"

let suite cases =
"suite">:::
  (List.map (fun x -> "test">:: test x) cases)


let satisfying ?timeout:(t=1000) p g =
  let r = ref t in
  retry (g >|= fun x -> if p x then Some x else
			  begin
			    r := !r - 1;
			    if !r = 0 then
			      failwith "failed to satisfy predicate"
			    else
			      None
			  end)

let gen_names n0 =
  int n0 >>= fun pos_main ->
  let rec aux n =
    if n <= 0 then return [] else
      aux (n - 1) >>= fun l ->
      if (n - 1) = pos_main then
	return (c_main :: l)
      else
	satisfying (fun m -> m <> c_main && not (List.mem m l)) small_int >|= fun m ->
	(m :: l)
  in
  aux n0

let gen_interface c exports =
  let gen_import =
    satisfying (fun (c', _) -> c' <> c) (among exports) >>= fun (c', e) ->
    int e >|= fun p ->
    (c', p)
  in
  list gen_import >|= fun l ->
  { name = c; export = List.assoc c exports; import = l }

let rec combine (l: 'a t list): 'a list t =
  match l with
  | [] -> return []
  | g :: gs -> combine gs >>= fun l ->
	       g >>= fun x ->
	       return (x :: l)

let is_gen =
  (2 -- 10) >>= fun n ->
  gen_names n >>= fun cs ->
  list_repeat n (1 -- 15) >>= fun exports ->
  combine (List.map (fun c -> gen_interface c (List.combine cs exports)) cs)

type call_type = Internal | External

let t_gen n0 prg_is ctx_is =
  let opponent player = match player with Prg -> Ctx | Ctx -> Prg in
  let first_player =
    if List.exists (fun (c: component_interface) -> c.name = c_main) prg_is then Prg else Ctx
  in
  let gen_player = QCheck.Arbitrary.(return Ctx ||| return Prg) in
  let call player =
    gen_player >>= fun next_player ->
    let next_is = match next_player with Prg -> prg_is | Ctx -> ctx_is in
    among next_is >>= fun component ->
    int component.export >>= fun p ->
    if next_player = player then
      return (Int (IntCall(component.name, p), player), (Internal, player))
    else
      small_int >|= fun i -> (Ext (ExtCall(component.name, p, i), player), (External, player))
  in
  let ret kind player =
    match kind with
    | Internal -> return (Int (IntRet, player))
    | External -> begin small_int >|= fun n -> Ext (ExtRet n, player) end
  in
  let internal_step player = return (Int (IntTau, player)) in
  let termination player = return (Ext (Term, player)) in
  let alpha_gen call_stack =
    let default_choices player =
      [
	call player >|= begin fun (alpha, frame) -> (alpha, Some (frame :: call_stack)) end;
	termination player >|= begin fun alpha -> (alpha, None) end;
	internal_step player >|= begin fun alpha -> (alpha, Some call_stack) end
      ]
    in
    match call_stack with
    | [] -> choose (default_choices first_player)
    | (kind, prev_player) :: call_stack' ->
       let player = match kind with Internal -> prev_player | External -> opponent prev_player in
       choose (
	   begin ret kind player >|= fun alpha -> (alpha, Some call_stack') end
	   :: default_choices player
	 )
  in
  let rec aux n call_stack_opt t =
    match (n, call_stack_opt) with
    | (_, None)
    | (0, _) ->
       return t
    | (_, Some call_stack) ->
       begin
	 if n = 1 then
	   satisfying (fun (alpha,_) -> match alpha with | Ext _ -> true | Int _ -> false)
		      (alpha_gen call_stack)
	 else
	   alpha_gen call_stack
       end >>= fun (alpha, call_stack_opt') ->
      aux (n - 1) call_stack_opt' (alpha :: t)
  in
  aux (n0 + 1) (Some []) [] >|= fun l -> (List.rev (List.tl l), List.hd l)

let rec split l =
  match l with
  | [] -> return ([], [])
  | x :: xs ->
     split xs >>= fun (l1, l2) ->
     bool >|= fun b ->
     if b then (x :: l1, l2) else (l1, x :: l2)

let case_gen n =
  let non_empty (is1, is2) =
    match (is1, is2) with | ([], _) | (_, []) -> false | _ -> true
  in
  is_gen >>= fun is ->
  satisfying non_empty (split is) >>= fun (is1, is2) ->
  t_gen n is1 is2 >>= fun (t, alpha) ->
  match alpha with
  | Ext (_, Prg) ->
     return (is2, t, alpha)
  | Ext (ea, Ctx) ->
     return (is1, dual t, Ext (ea, Prg))
  | _ ->
     failwith "dead code"

let _ =
  run_test_tt_main (suite (generate ~n:150 (case_gen 100)))
