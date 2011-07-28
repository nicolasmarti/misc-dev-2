open Def;;

(*
  quantified free variables:
  variables which are added to the ctxt after typechecking quantifier
  (implies we really need the env)

  - needed for shifting substitution, in order to apply them bellow quantifiers / pattern
*)

(* the quantified free variables in quantifiers *)
let rec quantifier_qfvars (q: quantifier) : (name * term) list =
  let (ps, ty, n) = q in
  List.fold_left (fun acc hd -> pattern_qfvars hd @ acc) [] ps

(* the quantified free variables (together with there type) in patterns 
   there is an order !!!
   (same as debruijn index)
*)

and pattern_qfvars (p: pattern) : (name * term) list =
  match p with
    | PVar (n, ty) -> [(n, ty)]
    | PAlias (n, p, ty) -> (n, ty)::pattern_qfvars p
    | PApp (f, arg, _) -> List.fold_left (fun acc hd -> pattern_qfvars hd @ acc) (pattern_qfvars f) (List.map fst arg)
    | _ -> []

;;

(*
  get the size 
*)
let quantifier_fqvars_size (q: quantifier) : int =
  List.length (quantifier_qfvars q)
;;

let pattern_fqvars_size (p: pattern) : int =
  List.length (pattern_qfvars p)
;;

module IndexMap = Map.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

(*
  grab the freevariables of a term
  no needs for order, so we use a set
*)
module IndexSet = Set.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;


let rec fv_term (te: term) : IndexSet.t =
  match te with
    | Type u -> IndexSet.empty
    | Var (Right i) when i < 0 -> IndexSet.singleton i
    | Var (Right i) when i >= 0 -> IndexSet.empty
    | AVar (Some i) -> IndexSet.singleton i
    | Cste c -> raise (Failure "NYI")
    | Obj o -> IndexSet.empty
    | Impl (q, te) -> IndexSet.union (fv_quantifier q) (fv_term te)
    | Lambda (qs, te) -> 
      List.fold_left (fun acc hd -> 
	IndexSet.union acc (fv_quantifier hd)
      ) (fv_term te) qs
    | Let (_, defs, te) ->
      List.fold_left (fun acc (_, hd) -> 
	IndexSet.union acc (fv_term hd)
      ) (fv_term te) defs
    | Ifte (t1, t2, t3) ->
      IndexSet.union (fv_term t1) (IndexSet.union (fv_term t2) (fv_term t3))
    | App (f, args) ->
      List.fold_left (fun acc (hd, _) -> 
	IndexSet.union acc (fv_term hd)
      ) (fv_term f) args
    | Case (te, eqs) ->
      List.fold_left (fun acc hd -> 
	IndexSet.union acc (fv_equation hd)
      ) (fv_term te) eqs
    | TyAnnotation (te, ty) ->
      IndexSet.union (fv_term te) (fv_tyAnnotation ty)
    | SrcInfo (te, _) -> fv_term te
    | _ -> raise (Failure "fv_term: not supported term")

and fv_quantifier (q: quantifier) : IndexSet.t =
  let (_, ty, _) = q in
  fv_tyAnnotation ty
and fv_tyAnnotation (ty: tyAnnotation) : IndexSet.t =
  match ty with
    | NoAnnotation -> IndexSet.empty
    | Infered te | Annotated te -> fv_term te
and fv_equation (eq: equation) : IndexSet.t =
  match eq with
    | NotGuarded (p, te) -> fv_term te
    | Guarded (p, dess) ->
      List.fold_left (fun acc (_, hd) ->
	IndexSet.union acc (fv_term hd)
      ) IndexSet.empty dess      
;;

(* build an Impl *)
let build_impl (qs: quantifier list) (ty: term) =
  List.fold_right (fun hd acc -> Impl (hd, acc)) qs ty
;;

let make_hiddens (qs: quantifier list) =
  List.map (fun (ps, ty, _) -> (ps, ty, Hidden)) qs
;;
