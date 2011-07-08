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

