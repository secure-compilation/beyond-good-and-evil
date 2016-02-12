(* A context language provides operations on programs taken from type
   [cl_program] and contexts taken from type [cl_context]. *)
Class context_language (cl_program: Type) (cl_context: Type): Type :=
  {
    cl_insert: cl_context -> cl_program -> cl_program;
    cl_compatible: cl_context -> cl_program -> Prop;
    cl_complete: cl_program -> Prop;
    cl_stat_eq: cl_program -> cl_program -> Prop;
    cl_beh_eq: cl_program -> cl_program -> Prop;
    (* Put relevant hypotheses here *)
    cl_stat_eq_compatible_complete:
      forall P Q,
        cl_stat_eq P Q ->
        (forall A,
           cl_compatible A P /\ cl_complete (cl_insert A P) ->
           cl_compatible A Q /\ cl_complete (cl_insert A Q))
  }.

Definition full_abstraction
           {source_program source_context: Type}
           {target_program target_context: Type}

           (source_cl: context_language source_program source_context)
           (target_cl: context_language target_program target_context)
           (cl_compile: source_program -> target_program): Prop :=
  forall P Q,
    cl_stat_eq P Q ->
    ((forall A, cl_compatible A P /\ cl_complete (cl_insert A P) ->
                cl_beh_eq (cl_insert A P) (cl_insert A Q))
     <->
     (forall a, cl_compatible a (cl_compile P) /\ cl_complete (cl_insert a (cl_compile P)) ->
                cl_beh_eq (cl_insert a (cl_compile P)) (cl_insert a (cl_compile Q)))).

(* A context language can be structured. It is the case when programs
   and contexts can have a shape. The shape characterizes the
   structure of the program or context. *)
Class structured_context_language
      {scl_program scl_context: Type}

      (scl_cl: context_language scl_program scl_context)
      (scl_shape: Type)
: Type :=
  {
    scl_program_has_shape: scl_shape -> scl_program -> Prop;
    scl_context_has_shape: scl_shape -> scl_context -> Prop
    (* Put relevant hypotheses here *)
  }.

Definition structured_full_abstraction
           {source_scl_program source_scl_context: Type}
           {target_scl_program target_scl_context: Type}
           {source_scl_cl: context_language source_scl_program source_scl_context}
           {target_scl_cl: context_language target_scl_program target_scl_context}
           {scl_shape: Type}

           (source_scl: structured_context_language source_scl_cl scl_shape)
           (target_scl: structured_context_language target_scl_cl scl_shape)
           (scl_compile: source_scl_program -> target_scl_program): Prop :=
  forall (s: scl_shape) (PP QQ: source_scl_program),
    cl_stat_eq PP QQ /\ scl_program_has_shape s PP /\ scl_program_has_shape s QQ ->
    ((forall AA,
        scl_context_has_shape s AA /\ cl_compatible AA PP /\ cl_complete (cl_insert AA PP) ->
        cl_beh_eq (cl_insert AA PP) (cl_insert AA QQ))
     <->
     (forall aa,
        scl_context_has_shape s aa /\
        cl_compatible aa (scl_compile PP) /\ cl_complete (cl_insert aa (scl_compile PP)) ->
        cl_beh_eq (cl_insert aa (scl_compile PP)) (cl_insert aa (scl_compile QQ)))).

(* A structured context language can be a structured variant of
   another (unstructured) context language. In this case one can
   "destruct" programs and contexts, i.e. forget their structure. *)
Class structured_variant
      {cl_program cl_context: Type}
      {scl_program scl_context: Type}
      {scl_cl: context_language scl_program scl_context}
      {scl_shape: Type}

      (cl: context_language cl_program cl_context)
      (scl: structured_context_language scl_cl scl_shape)
: Type :=
  {
    sv_destruct_program: scl_program -> cl_program;
    sv_destruct_context: scl_context -> cl_context
    (* Put relevant hypotheses here *)
  }.

(* There can be a link between (1) a compiler between structured
   languages and (2) a compiler between their unstructured
   variants. *)
Class structural_link
      {source_cl_program source_cl_context: Type}
      {source_scl_program source_scl_context: Type}
      {source_scl_cl: context_language source_scl_program source_scl_context}
      {target_cl_program target_cl_context: Type}
      {target_scl_program target_scl_context: Type}
      {target_scl_cl: context_language target_scl_program target_scl_context}
      {scl_shape: Type}
      {source_cl: context_language source_cl_program source_cl_context}
      {source_scl: structured_context_language source_scl_cl scl_shape}
      {target_cl: context_language target_cl_program target_cl_context}
      {target_scl: structured_context_language target_scl_cl scl_shape}

      (source_sv: structured_variant source_cl source_scl)
      (target_sv: structured_variant target_cl target_scl)
      (cl_compile: source_cl_program -> target_cl_program)
      (scl_compile: source_scl_program -> target_scl_program)
: Type :=
  {
    (* Put relevant hypotheses here *)
    (*forall PP, sv_destruct_program (scl_compile PP)
               =
               cl_compile (sv_destruct_program PP) *)
  }.

(* When there is a structural link between compilers, full abstraction
   for the unstructured one follows from structured full abstraction
   for the structured compiler. *)
Conjecture structured_full_abstraction_implies_full_abstraction : forall
        {source_cl_program source_cl_context: Type}
        {source_scl_program source_scl_context: Type}
        {source_scl_cl: context_language source_scl_program source_scl_context}
        {target_cl_program target_cl_context: Type}
        {target_scl_program target_scl_context: Type}
        {target_scl_cl: context_language target_scl_program target_scl_context}
        {scl_shape: Type}
        {source_cl: context_language source_cl_program source_cl_context}
        {source_scl: structured_context_language source_scl_cl scl_shape}
        {target_cl: context_language target_cl_program target_cl_context}
        {target_scl: structured_context_language target_scl_cl scl_shape}

        (source_sv: structured_variant source_cl source_scl)
        (target_sv: structured_variant target_cl target_scl),
  forall cl_compile scl_compile,
      structural_link source_sv target_sv cl_compile scl_compile ->
      structured_full_abstraction source_scl target_scl scl_compile ->
      full_abstraction source_cl target_cl cl_compile.
