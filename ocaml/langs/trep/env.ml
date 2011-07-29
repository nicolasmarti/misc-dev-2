open Def;;
open Misc;;
open Substitution;;

(* push a (typed) pattern / frame in an environment *)
let env_push_pattern (ctxt: env) (p: pattern) : env =
  let l = pattern_qfvars p in
  { frames = {empty_frame with qvs = l; pattern = p}::ctxt.frames }
;;

(* pop a pattern / frame from the environment *)
let rec env_pop_pattern (ctxt: env) : env * pattern =
  match ctxt.frames with
    (* for poping, here, we need to have a "clean" frame *)
    (* extension: accept a list of free variable,
       abstract l in the free vars, 
       return a substitution, from the free var, to app of freevar to l       
    *)
    | { qvs = l;
	pattern = p;
	fvs = [];
	decls = [];
	terms = [];
	equations = [];
	annotations = [];
	natures = [];
      }::tl -> 
      ({frames = tl}, p)
    | _ -> raise (Failure "Case not yet supported")
;;

let env_push_termstack (ctxt: env) (te: term) : env =
  match ctxt.frames with
    | hd::tl  ->
      {frames = {hd with terms = te::hd.terms}::tl}
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

let env_pop_termstack (ctxt: env) : env * term =
  match ctxt.frames with
    | hd::tl -> (
      match hd.terms with
	| thd::ttl ->	  
	  ({frames = {hd with terms = ttl}::tl}, thd)
	| _ -> raise (Failure "Catastrophic: no term to pop")
    )
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

let env_push_annotation (ctxt: env) (ty: tyAnnotation) : env =
  match ctxt.frames with
    | hd::tl  ->
      {frames = {hd with annotations = ty::hd.annotations}::tl}
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

let env_pop_annotation (ctxt: env) : env * tyAnnotation =
  match ctxt.frames with
    | hd::tl -> (
      match hd.annotations with
	| thd::ttl ->	  
	  ({frames = {hd with annotations = ttl}::tl}, thd)
	| _ -> raise (Failure "Catastrophic: no annotation to pop")
    )
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

let env_push_nature (ctxt: env) (n: nature) : env =
  match ctxt.frames with
    | hd::tl  ->
      {frames = {hd with natures = n::hd.natures}::tl}
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

let env_pop_nature (ctxt: env) : env * nature =
  match ctxt.frames with
    | hd::tl -> (
      match hd.natures with
	| thd::ttl ->	  
	  ({frames = {hd with natures = ttl}::tl}, thd)
	| _ -> raise (Failure "Catastrophic: no nature to pop")
    )
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

(* push a (typed) quantifier in an environment *)
let env_push_quantifier (ctxt: env) (q: quantifier) : env =
  (* we grab the patterns, and type annotation *)
  let (ps, ty, n) = q in
  (* we push the annotation *)
  let ctxt = env_push_annotation ctxt ty in
  let ctxt = env_push_nature ctxt n in
  List.fold_left env_push_pattern ctxt ps
;;

let rec fold_leftn (f: 'b -> 'b) (acc: 'b) (n: int) : 'b =
  if n < 0 then
    acc
  else
    fold_leftn f (f acc) (n-1)
;; 

(* pop a quantifier from an environment *)
let rec env_pop_quantifier (ctxt: env) (size: int) : env * quantifier =
  let (ctxt, ps) = fold_leftn (fun (ctxt, ps) ->
    let (ctxt, p) = env_pop_pattern ctxt in
    (ctxt, p::ps)
  ) (ctxt, []) size in
  let (ctxt, ty) = env_pop_annotation ctxt in
  let (ctxt, n) = env_pop_nature ctxt in
  (ctxt, (ps, ty, n))  
;;

let rec foldleft_maybe (f: 'c -> 'a -> ('b, 'c) either) (acc: 'c) (l: 'a list) : 'b option =
  match l with
    | [] -> None
    | hd::tl -> 
      match f acc hd with
	| Right nxt -> foldleft_maybe f nxt tl
	| Left res -> Some res
;;

(* get the debruijn index of a quantified variable *)
let qv_debruijn (ctxt: env) (name: string) : (index * term) option =
  foldleft_maybe 
    (fun curr_index frame -> 
      let index_in_frame = foldleft_maybe (fun curr_index (n, ty) -> 
	if n = name then Left (curr_index, ty) else Right (curr_index + 1)	  
      ) curr_index frame.qvs in
      match index_in_frame with
	| None -> Right (curr_index + List.length frame.qvs)
	(* we need to shift the term (curr_index represent the total number of qvs in visited frames) *)
	| Some (index, ty) -> Left (index, shift_term ty curr_index)
    )
    0 ctxt.frames
;;

(* get the name and type of a quantified variable by index *)
let qv_name (ctxt: env) (i: index) : name * term =
  let res =
    foldleft_maybe 
      (fun curr_index frame -> 
	let type_in_frame = foldleft_maybe (fun curr_index (n, ty) -> 
	  if curr_index = i then Left (n, ty) else Right (curr_index + 1)	  
	) curr_index frame.qvs in
	match type_in_frame with
	  | None -> Right (curr_index + List.length frame.qvs)
	  (* we need to shift the term (curr_index represent the total number of qvs in visited frames) *)
	  | Some (name, ty) -> Left (name, shift_term ty curr_index)
      )
      0 ctxt.frames
  in
  match res with
    | None -> raise (Failure "no such indexed variable")
    | Some res -> res
;;

(* get the type of a declaration *)
let declaration_type (ctxt: env) (s: symbol) : term option =
  foldleft_maybe 
    (fun curr_index frame -> 
      let type_in_frame = foldleft_maybe (fun _ decl -> 
	match decl with
	  | Signature (s', ty) when s' = s -> Left ty
	  | Inductive (name, qs, ty, cons) -> (
	    match s with
	      | Name n when n = name ->
		Left (build_impl qs ty)
	      | _ -> 
		match foldleft_maybe (fun _ (s', ty) ->  if s = s' then Left (build_impl (make_hiddens qs) ty)       else Right ()) () cons with
		  | None -> Right  ()
		  | Some res -> Left res
	  )
	  | RecordDecl _ -> 
	    (* NYI: might need to change RecordDecl definition *)
	    Right ()
	  | _ -> Right ()
      ) () frame.decls in
      match type_in_frame with
	| None -> Right (curr_index + List.length frame.qvs)
	(* we need to shift the term (curr_index represent the total number of qvs in visited frames) *)
	| Some ty -> Left (shift_term ty curr_index)
    )
    0 ctxt.frames
;; 

let env_push_decl (ctxt: env) (decl: declaration) : env =
  match ctxt.frames with
    | hd::tl  ->
      {frames = {hd with decls = decl::hd.decls}::tl}
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

let env_pop_decl (ctxt: env) : env * declaration =
  match ctxt.frames with
    | hd::tl -> (
      match hd.decls with
	| thd::ttl ->	  
	  ({frames = {hd with decls = ttl}::tl}, thd)
	| _ -> raise (Failure "Catastrophic: no declaration to pop")
    )
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;

(* rubbish ... need to recompute size each time ... *)
let env_new_fv (ctxt: env) (ty: term) : env * index = 
  let newindex = List.fold_left (fun acc hd -> acc - List.length hd.fvs) (-1) ctxt.frames in  
  match ctxt.frames with
    | hd::tl -> (
      match hd.fvs with
	| thd::ttl ->	  
	  ({frames = {hd with fvs = (ty, None)::ttl}::tl}, newindex)
	| _ -> raise (Failure "Catastrophic: no declaration to pop")
    )
    | _ -> raise (Failure "Catastrophic: empty frame list")
;;
