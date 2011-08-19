(* for parsing *)
open Parser
(* for pretty printing *)
open Pprinter

open Printf


(*********************************)
(* Definitions of data structure *)
(*********************************)

type name = string

type op = Nofix
	  | Prefix of int
	  | Infix of int * associativity
	  | Postfix of int

type symbol = | Name of name
	      | Symbol of name * op

type index = int

type nature = Explicit
	      | Implicit

(* but in our case we only use 
   'a = term
   'b = context
   'c = defs
*)
class virtual ['a, 'b, 'c] tObj =
object 
  method uuid: int = 0
  method virtual get_name: string
  method virtual get_type: 'a
  method virtual pprint: unit -> token
  method virtual apply: 'c -> 'b -> ('a * nature) list -> 'a
end

type term = Type of pos
	    | Cste of symbol * pos
	    | Obj of (term, context, defs) tObj * pos

	    (* the Left name is only valid after parsing, and removed by typecheck*)
	    | TVar of index * pos
		
	    (* these constructors are only valide after parsing, and removed by typechecking *)
	    | AVar of pos
	    | TName of symbol * pos

	    | App of term * (term * nature) list * pos
	    | Impl of (symbol * term * nature * pos) * term * pos
	    | Lambda of (symbol * term * nature * pos) * term * pos

(* N.B.: all types are properly scoped w.r.t. bounded var introduce by "preceding" pattern *)
and pattern = PType of pos 
	      | PVar of name * term * pos
	      | PAVar of term * pos
	      | PCste of symbol * pos
	      | PAlias of name * pattern * term * pos
	      | PApp of (symbol * pos) * (pattern * nature) list * term * pos

and equation = pattern * term

(* context of a term *)
(* N.B.: all terms are of the level in which they appear *)
and frame = {
  (* the symbol of the frame *)
  symbol : symbol;
  (* its type *)
  ty: term;
  (* the nature of the quantification *)
  nature: nature;
  (* its value: most stupid one: itself *)
  value: term;
    
  (* the free variables 
     - the index (redundant information put for sake of optimization)
     - the type of the free variable
     - its corresponding value (by unification)
  *)
  fvs: (index * term * term) list;

  (* the stacks *)
  termstack: term list;
  naturestack: nature list;
  patternstack: pattern list;
  
}

(* context *)
and context = frame list

and value = Inductive of (symbol * term) list
	    | Axiom
	    | Constructor
	    | Equation of equation list

(* definitions *)
and defs = {
  (* here we store all id in a string *)
  (* id -> (symbol * type * equations) *)
  store : (string, (symbol * term * value)) Hashtbl.t;
  hist : symbol list;
}

let empty_frame = {
  symbol = Symbol ("_", Nofix);
  ty = Type nopos;
  nature = Explicit;
  value = TVar (0, nopos);
  fvs = [];
  termstack = [];
  naturestack = [];
  patternstack = [];
}

(* the context must a least have one frame, for pushing/poping stack elements *)
let empty_context = empty_frame::[]
	   

let empty_defs = { store = Hashtbl.create 30; hist = [] }

type doudou_error = NegativeIndexBVar of index
		    | Unshiftable_term of term * int * int

		    | UnknownCste of symbol
		    | UnknownBVar of index * context
		    | UnknownFVar of index * context

		    | UnknownUnification of context * term * term
		    | NoUnification of context * term * term

		    | NoMatchingPattern of context * pattern * term

		    | PoppingNonEmptyFrame of frame

		    | CannotInfer of context * term * doudou_error
		    | CannotTypeCheck of context * term * term * term * doudou_error

		    | FreeError of string

exception DoudouException of doudou_error


(******************)
(*      misc      *)
(******************)

(* the last element of the list *)
let rec last (l: 'a list) : 'a =
  match l with 
    | [] -> raise (Failure "last: empty list")
    | hd::[] -> hd
    | hd :: tl -> last tl

(* take and drop as in haskell *)
let rec take (n: int) (l: 'a list) :'a list =
  match n with
    | 0 -> []
    | i when i < 0 -> raise (Invalid_argument "take")
    | _ -> 
      match l with
	| [] -> []
	| hd::tl -> hd::take (n-1) tl

let rec drop (n: int) (l: 'a list) :'a list =
  match n with
    | 0 -> l
    | i when i < 0 -> raise (Invalid_argument "drop")
    | _ -> 
      match l with
	| [] -> []
	| hd::tl -> drop (n-1) tl

(* build a list of the same element of size n *)
let rec replicate (e: 'a) (n: int) : 'a list =
  match n with
    | _ when n < 0 -> raise (Failure "replicate")
    | 0 -> []
    | _ -> e :: replicate e (n-1)

(* some traverse fold without the reverse *)
let mapacc (f: 'b -> 'a -> ('c * 'b)) (acc: 'b) (l: 'a list) : 'c list * 'b =
  let acc = ref acc in
  (List.map (fun hd -> let (hd, acc') = f !acc hd in
		       acc := acc';
		       hd) l, !acc)

(* some map which also gives the remaining list *)
let rec map_remain (f: 'a -> 'a list -> 'b) (l: 'a list) : 'b list =
  match l with
    | [] -> []
    | hd::tl ->
      let hd = f hd tl in
      hd :: map_remain f tl


type ('a, 'b) either = Left of 'a
		       | Right of 'b
;;

(* a fold that might stop before the whole traversal *)
let rec fold_stop (f: 'b -> 'a -> ('b, 'c) either) (acc: 'b) (l: 'a list) : ('b, 'c) either =
  match l with
    | [] -> Left acc
    | hd::tl ->
      match f acc hd with
	| Left acc -> fold_stop f acc tl
	| Right res -> Right res

(* a fold that returns an update of the traversed list *)
let rec fold_cont (f: 'b -> 'a list -> 'a list * 'b) (acc: 'b) (l: 'a list): 'b =
  match l with
    | [] -> acc
    | _ -> 
      let l', acc = f acc l in
      fold_cont f acc l'

(* a function called n times with arguments pushed in a list *)
let rec map_nth (f: int -> 'a) (n: int) : 'a list =
  match n with
    | i when i < 0 -> []
    | 0 -> []
    | _ ->
      let res = f n in
      res::map_nth f (n - 1)

(* assert that pos1 contains pos2 *)
let pos_in (pos1: pos) (pos2: pos) : bool =
  let ((begin_line1, begin_col1), (end_line1, end_col1)) = pos1 in
  let ((begin_line2, begin_col2), (end_line2, end_col2)) = pos2 in
  (* the start of pos2 must be equal or after the start of pos1 *)
  ((begin_line2 > begin_line1) || (begin_line1 = begin_line2 && begin_col2 >= begin_col1))
  (* and the end of pos2 must be equal or before the end of pos 1*)
  && ((end_line2 < end_line1) || (end_line1 = end_line2 && end_col2 <= end_col1))

(* choose a position between two possibilities *)
let best_pos (p1: pos) (p2: pos) : pos =
  match p1, p2 with
    | _ when p1 = nopos -> p2
    | _ when p2 = nopos  -> p1
    | _ when pos_in p1 p2 -> p2
    | _ -> p1

(* returns the numbers of bvars introduced by a pattern 
   we should always have 
   pattern_size p = List.length (fst (pattern_bvars p)))
*)
let rec pattern_size (p: pattern) : int =
  match p with
    | PType _-> 0
    | PVar _ -> 1
    | PAVar _ -> 1
    | PCste _ -> 0
    | PAlias (_, p, _, _) -> 1 + pattern_size p
    | PApp (_, args, _, _) -> 
      List.fold_left ( fun acc (hd, _) -> acc + pattern_size hd) 0 args

(* computation of free variable in a term *)
module IndexSet = Set.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

(* set the outermost pattern type *)
let set_pattern_type (p: pattern) (ty: term) : pattern =
  match p with
    | PVar (n, _, pos) -> PVar (n, ty, pos)
    | PAVar (_, pos) -> PAVar (ty, pos)
    | PAlias (n, p, _, pos) -> PAlias (n, p, ty, pos)
    | PApp (s, args, _, pos) -> PApp (s, args, ty, pos)
    | _ -> p    

(* set the outermost pattern position *)
let set_pattern_pos (p: pattern) (pos: pos) : pattern =
  match p with
    | PType _ -> PType pos
    | PVar (n, ty, _) -> PVar (n, ty, pos)
    | PAVar (ty, _) -> PAVar (ty, pos)
    | PCste (s, _) -> PCste (s, pos)
    | PAlias (n, p, ty, _) -> PAlias (n, p, ty, pos)
    | PApp (s, args, ty, _) -> PApp (s, args, ty, pos)

(* get the outermost pattern position *)
let get_pattern_pos (p: pattern) : pos =
  match p with
    | PType pos -> pos
    | PVar (_, _, pos) -> pos
    | PAVar (_, pos) -> pos
    | PCste (_, pos) -> pos
    | PAlias (_, _, _, pos) -> pos
    | PApp (_, _, _, pos) -> pos

(* set the outermost term position *)
let set_term_pos (te: term) (p: pos) : term =
    match te with
      | Type _ -> Type p
      | Cste (s, _) -> Cste (s, p)
      | Obj (o, _) -> Obj (o, p)
      | TVar (i, _) -> TVar (i, p)
      | AVar _ -> AVar p
      | TName (s, _) -> TName (s, p)
      | App (f, args, _) -> App (f, args, p)
      | Impl (q, te, _) -> Impl (q, te, p)
      | Lambda (q, te, _) -> Lambda (q, te, p)

(* set the outermost term position *)
let get_term_pos (te: term) : pos =
    match te with
      | Type p -> p
      | Cste (_, p) -> p
      | Obj (_, p) -> p
      | TVar (_, p) -> p
      | AVar p -> p
      | TName (_, p) -> p
      | App (_, _, p) -> p
      | Impl (_, _, p) -> p
      | Lambda (_, _, p) -> p

(* the set of free variable in a term *)
let rec fv_term (te: term) : IndexSet.t =
  match te with
    | Type _ | Cste _ | Obj _ -> IndexSet.empty
    | TVar (i, _) when i >= 0 -> IndexSet.empty
    | TVar (i, _) when i < 0 -> IndexSet.singleton i
    | AVar _ -> IndexSet.empty
    | TName _ -> IndexSet.empty
    | App (te, args, _) ->
      List.fold_left (fun acc (te, _) -> IndexSet.union acc (fv_term te)) (fv_term te) args
    | Impl ((s, ty, n, pos), te, _) ->
      IndexSet.union (fv_term ty) (fv_term te)
    | Lambda ((s, ty, n, pos), te, _) ->
      IndexSet.union (fv_term ty) (fv_term te)

and fv_pattern (p: pattern) : IndexSet.t =
  match p with
    | PType _ | PCste _ -> IndexSet.empty
    | PVar (_, ty, _) -> fv_term ty
    | PAVar (ty, _) -> fv_term ty
    | PAlias (_, p, ty, _) -> IndexSet.union (fv_term ty) (fv_pattern p)
    | PApp (_, args, ty, _) ->
      List.fold_left (fun acc (p, _) -> IndexSet.union acc (fv_pattern p)) (fv_term ty) args

(* shift a set of variable *)
let shift_vars (vars: IndexSet.t) (delta: int) : IndexSet.t =
  IndexSet.fold (fun e acc ->
    if (e >= 0 && e + delta < 0) || e < 0 then acc
    else IndexSet.add (e + delta) acc      
  ) vars IndexSet.empty


(* the set of bound variable in a term *)
let rec bv_term (te: term) : IndexSet.t =
  match te with
    | Type _ | Cste _ | Obj _ -> IndexSet.empty
    | TVar (i, _) when i >= 0 -> IndexSet.singleton i
    | TVar (i, _) when i < 0 -> IndexSet.empty
    | AVar _ -> IndexSet.empty
    | TName _ -> IndexSet.empty
    | App (te, args, _) ->
      List.fold_left (fun acc (te, _) -> IndexSet.union acc (bv_term te)) (bv_term te) args
    | Impl ((s, ty, n, pos), te, _) ->
      IndexSet.union (bv_term ty) (shift_vars (bv_term te) (-1))
    | Lambda ((s, ty, n, pos), te, _) ->
      IndexSet.union (bv_term ty) (shift_vars (bv_term te) (-1))

and bv_pattern (p: pattern) : IndexSet.t =
  match p with
    | PType _ | PCste _ -> IndexSet.empty
    | PVar (_, ty, _) -> (shift_vars (bv_term ty) (-1))
    | PAVar (ty, _) -> (shift_vars (bv_term ty) (-1))
    | PAlias (_, p, ty, _) -> IndexSet.union (shift_vars (bv_term ty) (- (pattern_size p))) (bv_pattern p)
    | PApp (_, args, ty, _) ->
      let i, vars = List.fold_left (fun (i, acc) (p, _) ->
	i - pattern_size p, IndexSet.union acc (shift_vars (bv_pattern p) i)
      ) (0, IndexSet.empty) args in
      IndexSet.union vars (shift_vars (bv_term ty) i)

(* function like map, but that can skip elements *)
let rec skipmap (f: 'a -> 'b option) (l: 'a list) : 'b list =
  match l with
    | [] -> []
    | hd::tl -> 
      match f hd with
	| None -> skipmap f tl
	| Some hd -> hd::(skipmap f tl)

(* function that map symbol into string *)
let symbol2string (s: symbol) =
  match s with
    | Name n -> n
    | Symbol (n, o) ->
      let (pre, post) = 
	match o with
	  | Nofix -> "", ""
	  | Prefix _ -> "[", ")"
	  | Infix _ -> "(", ")"
	  | Postfix _ -> "(", "]"
      in
      String.concat "" [pre; n; post]

(* get a bound variable frame *)
let get_bvar_frame (ctxt: context) (i: index) : frame =
  try 
    List.nth ctxt i
  with
    | Failure _ -> raise (DoudouException (UnknownBVar (i, ctxt)))
    | Invalid_argument _ -> raise (DoudouException (NegativeIndexBVar i))

(*
  the priority of operators
  the greater, the more strongly binding
  Nofix have 0
*)
let op_priority (o: op) : int =
  match o with
    | Nofix -> 0
    | Prefix i -> i
    | Infix (i, _) -> i
    | Postfix i -> i

(* returns only the elements that are explicit *)
let filter_explicit (l: ('a * nature) list) : 'a list =
  List.map fst (List.filter (fun (_, n) -> n = Explicit) l)

(* utilities for DoudouException *)
(* build an implication: no shifting in types !!! *)
let build_impl (symbols: (symbol * pos) list) (ty: term) (nature: nature) (body: term) : term =
  List.fold_right (fun (s, pos) acc -> Impl ((s, ty, nature, pos), acc, (fst pos, snd (get_term_pos acc)))) symbols body

(* build a Lambda: no shifting in types !!! *)
let build_lambda (symbols: (symbol * pos) list) (ty: term) (nature: nature) (body: term) : term =
  List.fold_right (fun (s, pos) acc -> Lambda ((s, ty, nature, pos), acc, (fst pos, snd (get_term_pos acc)))) symbols body

(* build a Lambda: no shifting in types !!! *)
let build_lambdas (qs: ((symbol * pos) list * term * nature) list) (body: term) : term =
  List.fold_right (fun (s, ty, n) acc -> build_lambda s ty n acc) qs body

(* recursive destrution of impl and lanbdas *)
let rec destruct_impl (ty: term) : (symbol * term * nature * pos) list * term =
  match ty with
    | Impl (e, te, _) ->
      let l, te = destruct_impl te in
      e::l, te
    | _ -> [], ty

let rec lambda_impl (ty: term) : (symbol * term * nature * pos) list * term =
  match ty with
    | Lambda (e, te, _) ->
      let l, te = destruct_impl te in
      e::l, te
    | _ -> [], ty


(*************************************)
(*      substitution/rewriting       *)
(*************************************)

(* substitution = replace variables (free or bound) by terms (used for typechecking/inference with free variables, and for reduction with bound variable) *)

module IndexMap = Map.Make(
  struct
    type t = int
    let compare x y = compare x y
  end
);;

(* substitution: from free variables to term *) 
type substitution = term IndexMap.t;;

(* substitution *)
let rec term_substitution (s: substitution) (te: term) : term =
  match te with
    | Type _ | Cste _ | Obj _ -> te
    | TVar (i, _) as v -> 
      (
	try 
	  IndexMap.find i s 
	with
	  | Not_found -> v
      )
    | AVar _ -> raise (Failure "term_substitution catastrophic: AVar")
    | TName _ -> raise (Failure "term_substitution catastrophic: TName")
    | App (te, args, pos) ->
      App (term_substitution s te,
	   List.map (fun (te, n) -> term_substitution s te, n) args,
	   pos)
    | Impl ((symb, ty, n, p), te, pos) ->
      Impl ((symb, term_substitution s ty, n, p),
	    term_substitution (shift_substitution s 1) te,
	    pos)
    | Lambda ((symb, ty, n, p), te, pos) ->
      Lambda ((symb, term_substitution s ty, n, p),
	      term_substitution (shift_substitution s 1) te,
	      pos)

and pattern_substitution (s: substitution) (p: pattern) : pattern =
  match p with
    | PType _ | PCste _ -> p
    | PVar (n, ty, pos) -> PVar (n, term_substitution s ty, pos)
    | PAlias (n, p, ty, pos) -> PAlias (n, pattern_substitution s p, term_substitution (shift_substitution s (pattern_size p)) ty, pos)
    | PApp (symb, args, ty, pos) ->
      PApp (symb,
	    fst (
	      List.fold_left (fun (args, s) (p, n) ->
		args @ [pattern_substitution s p, n], shift_substitution s (pattern_size p)
	      ) ([], s) args
	    ),
	    term_substitution (shift_substitution s (pattern_size p)) ty,
	    pos)

(* shift vars index in a substitution 
   only bound variable of the l.h.s. of the map are shifted too
*)
and shift_substitution (s: substitution) (delta: int) : substitution =
  IndexMap.fold (fun key value acc -> 
    try 
      if key < 0 then 
	IndexMap.add key (shift_term value delta) acc
      else 
	if key + delta < 0 then acc else IndexMap.add (key + delta) (shift_term value delta) acc 
    with
      | DoudouException (Unshiftable_term _) -> acc
  ) s IndexMap.empty
      
(* shift bvar index in a term *)
and shift_term (te: term) (delta: int) : term =
  leveled_shift_term te 0 delta

(* shift bvar index in a term, above a given index *)
and leveled_shift_term (te: term) (level: int) (delta: int) : term =
  match te with
    | Type _ | Cste _ | Obj _ | AVar _ | TName _ -> te
    | TVar (i, _) when i < 0 -> te
    | TVar (i, pos) as v when i >= 0 ->
      if i >= level then
	if i + delta < level then (
	  raise (DoudouException (Unshiftable_term (te, level, delta)))
	)
	else
	  TVar (i + delta, pos)
      else
	v

    | App (te, args, pos) ->
      App (
	leveled_shift_term te level delta,
	List.map (fun (te, n) -> leveled_shift_term te level delta, n) args,
	pos
      )
    | Impl ((s, ty, n, p), te, pos) ->
      Impl ((s, leveled_shift_term ty level delta, n, p), leveled_shift_term te (level + 1) delta,
	    pos)

    | Lambda ((s, ty, n, p), te, pos) ->
      Lambda ((s, leveled_shift_term ty level delta, n, p), leveled_shift_term te (level + 1) delta, pos)

and leveled_shift_pattern (p: pattern) (level: int) (delta: int) : pattern =
  match p with
    | PType _ | PCste _ -> p
    | PVar (n, ty, pos) -> PVar (n, leveled_shift_term ty level delta, pos)
    | PAVar (ty, pos) -> PAVar (leveled_shift_term ty level delta, pos)
    | PAlias (s, p, ty, pos) -> PAlias (s, leveled_shift_pattern p level delta, leveled_shift_term ty (level + pattern_size p) delta, pos)
    | PApp (s, args, ty, pos) ->
      PApp (s,
	    fst (
	      List.fold_left (fun (args, level) (p, n) ->
		args @ [leveled_shift_pattern p level delta, n], level + pattern_size p
	      ) ([], level) args
	    ),
	    leveled_shift_term ty (level + pattern_size p) delta, pos)


(********************************)
(*      defs/context/frame      *)
(********************************)

(* build a new frame 
   value is optional
*)
let build_new_frame (s: symbol) ?(value: term = TVar (0, nopos)) ?(nature: nature = Explicit) (ty: term) : frame =
{ 
  symbol = s;
  ty = ty;
  nature = nature;
  value = value;

  fvs = [];
  termstack = [];
  naturestack = [];
  patternstack = [];

}

(* push the bvars of a pattern in a context *)
let push_pattern_bvars (ctxt: context) (l: (name * term * term) list) : context =
  List.fold_left (fun ctxt (n, ty, v) ->
    (
      build_new_frame (Name n) ~value:v ty
    ) :: ctxt	     

  ) ctxt l


(* returns the list of bound variables, their value (w.r.t. other bound variable) and their type in a pattern    
   it also returns the overall value of the pattern (under the pattern itself)
   hd::tl -> hd is the "oldest" variable, and is next to be framed
*)

let rec pattern_bvars (p: pattern) : (name * term * term) list * term =
  match p with
    | PType pos -> [], Type pos
    | PVar (n, ty, pos) -> [n, ty, TVar (0, pos)], TVar (0, pos)
    | PAVar (ty, pos) -> ["_", ty, TVar (0, pos)], TVar (0, pos)
    | PCste (s, pos) -> [] , Cste (s, pos)
    | PAlias (n, p, ty, pos) -> 
      let l, te = pattern_bvars p in
      (* the value is shift by one (under the alias-introduced var) *)
      let te = shift_term te 1 in
	(l @ [n, ty, te], TVar (0, pos))
    | PApp ((s, p), args, ty, pos) -> 
      let (delta, l, rev_values) = 
	(* for sake of optimization the value list is in reverse order *)
	List.fold_left (fun (delta, l, rev_values) (p, n) ->
	  (* first we grab the result for p *)
	  let (pl, te) = pattern_bvars p in
	  (* then we need to shift the value term by the current delta level *)
	  let te = shift_term te delta in
	  (* we update the delta value, and returns the concatenation *)
	  (delta + List.length l, l @ pl, (te, n)::rev_values)
	) (0, [], []) args in
      (l, App (Cste (s, p), List.rev rev_values, pos))


(* compute the context under a pattern *)
let input_pattern (ctxt: context) (p: pattern) : context =
  (* we extract the list of bound variable in the pattern *)
  let (bvars, _) = pattern_bvars p in
  (* we build a new context with the pattern bvars frames pushed *)
  push_pattern_bvars ctxt bvars

(* apply a substitution in a context *)
let context_substitution (s: substitution) (ctxt: context) : context =
  fst (mapacc (fun s frame ->
    { frame with
      ty = term_substitution s frame.ty;
      value = term_substitution s frame.value;
      fvs = List.map (fun (index, ty, value) -> index, term_substitution s ty, term_substitution s value) frame.fvs;
      termstack = List.map (term_substitution s) frame.termstack;
      patternstack = List.map (pattern_substitution s) frame.patternstack
    }, shift_substitution s (-1)
  ) s ctxt
  )

(* retrieve the debruijn index of a bound var through its symbol *)
let bvar_lookup (ctxt: context) (s: symbol) : index option =
  let res = fold_stop (fun level frame ->
    if symbol2string frame.symbol = symbol2string s then
      Right level
    else
      Left (level + 1)
  ) 0 ctxt in
  match res with
    | Left _ -> None
    | Right level -> Some level

(* grab the value of a bound var *)
let bvar_value (ctxt: context) (i: index) : term =
  try (
    let frame = List.nth ctxt i in
    let value = frame.value in
    shift_term value i
  ) with
    | Failure "nth" -> raise (DoudouException (UnknownBVar (i, ctxt)))
    | Invalid_argument "List.nth" -> raise (DoudouException (NegativeIndexBVar i))

(* grab the type of a bound var *)
let bvar_type (ctxt: context) (i: index) : term =
  try (
    let frame = List.nth ctxt i in
    let ty = frame.ty in
    shift_term ty i
  ) with
    | Failure "nth" -> raise (DoudouException (UnknownBVar (i, ctxt)))
    | Invalid_argument "List.nth" -> raise (DoudouException (NegativeIndexBVar i))

(* grab the value of a free var *)
let fvar_value (ctxt: context) (i: index) : term =
  let lookup = fold_stop (fun level frame ->
    let lookup = fold_stop (fun () (index, ty, value) -> 
      if index = i then Right value else Left ()
    ) () frame.fvs in
    match lookup with
      | Left () -> Left (level + 1)
      | Right res -> Right (shift_term res level)
  ) 0 ctxt in
  match lookup with
    | Left _ -> raise (DoudouException (UnknownFVar (i, ctxt)))
    | Right res -> res

(* grab the type of a free var *)
let fvar_type (ctxt: context) (i: index) : term =
  let lookup = fold_stop (fun level frame ->
    let lookup = fold_stop (fun () (index, ty, value) -> 
      if index = i then Right ty else Left ()
    ) () frame.fvs in
    match lookup with
      | Left () -> Left (level + 1)
      | Right res -> Right (shift_term res level)
  ) 0 ctxt in
  match lookup with
    | Left _ -> raise (DoudouException (UnknownFVar (i, ctxt)))
    | Right res -> res

(* extract a substitution from the context *)
let context2substitution (ctxt: context) : substitution =
  fst (List.fold_left (
    fun (s, level) frame -> 
      let s = List.fold_left (fun s (index, ty, value) ->
	IndexMap.add index (shift_term value level) s
      ) s frame.fvs in
      (s, level+1)
  ) (IndexMap.empty, 0) ctxt
  )

(* pushing and poping terms in the term stack 
   N.B.: with side effect
*)
let push_terms (ctxt: context ref) (tes: term list) : unit =
  let (hd::tl) = !ctxt in
  ctxt := ({hd with termstack = tes @ hd.termstack})::tl

let pop_terms (ctxt: context ref) (sz: int) : term list =
  let (hd::tl) = !ctxt in  
  ctxt := ({hd with termstack = drop sz hd.termstack})::tl;
  take sz hd.termstack

(* pushing and poping natures in the nature stack 
   N.B.: with side effect
*)
let push_nature (ctxt: context ref) (n: nature) : unit =
  let (hd::tl) = !ctxt in
  ctxt := ({hd with naturestack = n :: hd.naturestack})::tl

let pop_nature (ctxt: context ref) : nature =
  let (hd::tl) = !ctxt in  
  ctxt := ({hd with naturestack = List.tl hd.naturestack})::tl;
  List.hd hd.naturestack

(* unfold a constante *)
let unfold_constante (defs: defs) (s: symbol) : value =
  try 
    (fun (_, _, value) -> value) (Hashtbl.find defs.store (symbol2string s))
  with
    | Not_found -> raise (DoudouException (UnknownCste s))

(* grab the type of a constante *)
let constante_type (defs: defs) (s: symbol) : term =
  try 
    (fun (_, ty, _) -> ty) (Hashtbl.find defs.store (symbol2string s))
  with
    | Not_found -> raise (DoudouException (UnknownCste s))

(* grab the real symbol of a constante *)
let constante_symbol (defs: defs) (s: symbol) : symbol =
  try 
    (fun (s, _, _) -> s) (Hashtbl.find defs.store (symbol2string s))
  with
    | Not_found -> raise (DoudouException (UnknownCste s))

(* pop a frame *)
let pop_frame (ctxt: context) : context * frame =
  match List.hd ctxt with
    | { fvs = []; termstack = []; naturestack = []; patternstack = []; _} ->
      List.tl ctxt, List.hd ctxt
    | { termstack = []; naturestack = []; patternstack = []; _} ->
      raise (Failure "Case not yet supported, pop_frame with still fvs")
    | _ -> raise (DoudouException (PoppingNonEmptyFrame (List.hd ctxt)))

(* poping frame: fst := resulting context, snd := poped frames *)
let rec pop_frames (ctxt: context) (nb: int) : context * context =
  if nb <= 0 then ctxt, [] else 
    let ctxt, frame = pop_frame ctxt in 
    let ctxt, frames = pop_frames ctxt (nb - 1) in
    ctxt, frame::frames

(* this function rewrite all free vars that have a real value in the upper frame of a context into a list of terms, and removes them *)
let rec flush_fvars (ctxt: context ref) (l: term list) : term list =
  let hd, tl = List.hd !ctxt, List.tl !ctxt in
  let (terms, fvs) = List.fold_left (fun (terms, fvs) (i, te, ty) ->
    match te with
      | TVar (i, _) ->
      (* there is not value for this free variable -> keep it *)
	terms, fvs @ [i, te, ty]
      | _ -> 
      (* there is a value, we can get rid of the free var *)
	let terms = List.map (fun hd -> term_substitution (IndexMap.singleton i te) hd) terms in
	terms, fvs
  ) (l, []) hd.fvs in
  ctxt := ({hd with fvs = fvs})::tl;
  terms

(* we add a free variable *)
let add_fvar (ctxt: context ref) (ty: term) : int =
  let next_fvar_index = 
    match (fold_stop (fun acc frame ->
      match frame.fvs with
	| [] -> Left acc
	| (i, _, _)::_ -> Right (i - 1)
    ) (-1) !ctxt)
    with
      | Left i -> i
      | Right i -> i
  in
  let frame = List.hd !ctxt in
  ctxt := ({ frame with fvs = (next_fvar_index, ty, TVar (next_fvar_index, nopos))::frame.fvs})::List.tl !ctxt;
  next_fvar_index

(* add definitions to a defs *)

let addAxiom (defs: defs ref) (s: symbol) (ty: term) : unit =
  (* just checking that there is no redefinition *)
  if Hashtbl.mem !defs.store (symbol2string s) then raise (DoudouException (FreeError (String.concat "" ["redefinition of symbol: "; (symbol2string s)])));

  (* update the definitions *)
  Hashtbl.add !defs.store (symbol2string s) (s, ty, Axiom);
  defs := {!defs with hist = s::!defs.hist }

let addEquation (defs: defs ref) (s: symbol) (eq: equation) : unit =
  (* just checking that there is a definition *)
  if not (Hashtbl.mem !defs.store (symbol2string s)) then raise (DoudouException (FreeError (String.concat "" ["symbol: "; (symbol2string s); " is not defined!"])));

  (* we verify that it is either an equation or an axioms*)
  let eqs = (match unfold_constante !defs s with
    | Axiom -> []
    | Equation eqs -> eqs
    | Inductive _ -> raise (DoudouException (FreeError (String.concat "" ["symbol: "; (symbol2string s); " is an Inductive Type!"])))
    | Constructor -> raise (DoudouException (FreeError (String.concat "" ["symbol: "; (symbol2string s); " is a constructor!"])))
  ) in
  (* update the definitions *)
  Hashtbl.add !defs.store (symbol2string s) (s, constante_type !defs s, Equation (eqs @ [eq]));
  defs := {!defs with hist = s::!defs.hist }
  
(******************)
(* pretty printer *)
(******************)

(*
  helper functions
*)
let rec intercalate (inter: 'a) (l: 'a list) : 'a list =
  match l with
    | hd1::hd2::tl ->
      hd1::inter::(intercalate inter (hd2::tl))
    | _ -> l

let rec intercalates (inter: 'a list) (l: 'a list) : 'a list =
  match l with
    | hd1::hd2::tl ->
      hd1::inter @ intercalates inter (hd2::tl)
    | _ -> l

let rec withParen (t: token) : token =
  Box [Verbatim "("; t; Verbatim ")"]

let rec withBracket (t: token) : token =
  Box [Verbatim "{"; t; Verbatim "}"]

(* a data structure to mark the place where the term/pattern is *)
type place = InNotation of op * int (* in the sndth place of the application to the notation with op *)
	     | InApp (* in the head of application *)
	     | InArg of nature (* as an argument (Explicit) *)
	     | InAlias  (* in an alias pattern *)
	     | Alone (* standalone *)

(* TODO: add options for 
   - printing implicit terms 
   - printing type annotation
   - source info
*)

type pp_option = {
  show_implicit : bool;
  show_indices : bool;
  show_position : bool;
}

let pp_option = ref {show_implicit = false; show_indices = false; show_position = false}

(* transform a term into a box *)
let rec term2token (ctxt: context) (te: term) (p: place): token =
  match te with
    | Type _ -> Verbatim "Type"
    | Cste (s, _) -> Verbatim (symbol2string s)
    | Obj (o, _) -> o#pprint ()
    | TVar (i, _) when i >= 0 -> 
      let frame = get_bvar_frame ctxt i in
      if !pp_option.show_indices then
	Box [Verbatim (symbol2string (frame.symbol)); Verbatim "["; Verbatim (string_of_int i); Verbatim "]"]
      else
	Verbatim (symbol2string (frame.symbol))
    | TVar (i, _) when i < 0 -> 
      Verbatim (String.concat "" ["?["; string_of_int i;"]"])

    (* we need to split App depending on the head *)
    (* the case for notation Infix *)
    | App (Cste (Symbol (s, Infix (myprio, myassoc)), _), args, _) when not !pp_option.show_implicit && List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 2->
      (* we should put parenthesis in the following condition: *)
      (match p with
	(* if we are an argument *)
	| InArg Explicit -> withParen
	(* if we are in a notation such that *)
	(* a prefix or postfix binding more  than us *)
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	(* or another infix with higher priority *)
	| InNotation (Infix (i, _), _) when i > myprio -> withParen
	(* or another infix with same priority depending on the associativity and position *)
	(* I am the second argument and its left associative *)
	| InNotation (Infix (i, LeftAssoc), 2) when i = myprio -> withParen
	(* I am the first argument and its right associative *)
	| InNotation (Infix (i, RightAssoc), 1) when i = myprio -> withParen

	(* else we do not need parenthesis *)
	| _ -> fun x -> x
      )	(
	match (if !pp_option.show_implicit then List.map fst args else filter_explicit args) with
	  | arg1::arg2::[] ->
	    let arg1 = term2token ctxt arg1 (InNotation (Infix (myprio, myassoc), 1)) in
	    let arg2 = term2token ctxt arg2 (InNotation (Infix (myprio, myassoc), 2)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg1; te; arg2])
	  | _ -> raise (Failure "term2token, App infix case: irrefutable patten")
       )
    (* the case for Prefix *)
    | App (Cste (Symbol (s, (Prefix myprio)), _), args, _) when not !pp_option.show_implicit &&List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a postfix notation more binding than us
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	| _ -> fun x -> x
      ) (
	match filter_explicit args with
	  | arg::[] ->
	    let arg = term2token ctxt arg (InNotation (Prefix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [te; arg])
	  | _ -> raise (Failure "term2token, App prefix case: irrefutable patten")
       )

    (* the case for Postfix *)
    | App (Cste (Symbol (s, (Postfix myprio)), _), args, _) when not !pp_option.show_implicit && List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a prefix notation more binding than us
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| _ -> fun x -> x
      ) (
	match filter_explicit args with
	  | arg::[] ->
	    let arg = term2token ctxt arg (InNotation (Postfix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg; te])
	  | _ -> raise (Failure "term2token, App postfix case: irrefutable patten")
       )

    (* if we have only implicit argument (and if we don't want to print them, then we are not really considered as a App  *)
    | App (te, args, _) when not !pp_option.show_implicit && List.length (filter_explicit args) = 0 ->
      term2token ctxt te p

    (* general case *)
    | App (te, args, _) ->
      (* we only embed in parenthesis if
	 - we are an argument of an application
      *)
      (match p with
	| InArg Explicit -> withParen
	| _ -> fun x -> x
      ) (
	let args = List.map (fun te -> term2token ctxt te (InArg Explicit)) (if !pp_option.show_implicit then List.map fst args else filter_explicit args) in
	let te = term2token ctxt te InApp in
	Box (intercalate (Space 1) (te::args))
       )

    (* implication *)
    | Impl ((s, ty, nature, _), te, _) ->
      (* we embed in parenthesis if 
	 - embed as some arg 
	 - ??
      *)
      (
	match p with
	  | InArg Explicit -> withParen
	  | _ -> fun x -> x
      )
	(
	  (* the lhs of the ->*)
	  let lhs = 
	    (* if the symbol is Nofix _ -> we skip the symbol *)
	    (* IMPORTANT: it means that Symbol ("_", Nofix)  as a special meaning !!!! *)
	    match s with
	      | Symbol ("_", Nofix) | _ when not (IndexSet.mem 0 (bv_term te))->
		(* we only put brackets if implicit *)
		(if nature = Implicit then withBracket else fun x -> x)
		  (term2token ctxt ty (InArg nature))
	      | _ -> 
		(* here we put the nature marker *)
		(if nature = Implicit then withBracket else withParen)
		  (Box [Verbatim (symbol2string s); Space 1; Verbatim "::"; Space 1; term2token ctxt ty Alone])
	  in 
	  (* for computing the r.h.s, we need to push a new frame *)
	  let newframe = build_new_frame s (shift_term ty 1) in
	  let rhs = term2token (newframe::ctxt) te Alone in
	  Box [lhs; Space 1; Verbatim "->"; Space 1; rhs]
	)

    (* quantification *)
    | Lambda ((s, ty, nature, _), te, _) ->
      (* we embed in parenthesis if 
	 - embed as some arg 
	 - ??
      *)
      (
	match p with
	  | InArg Explicit -> withParen
	  | _ -> fun x -> x
      )
	(
	  (* the lhs of the ->*)
	  let lhs = 
	    (* if the symbol is Nofix _ -> we skip the symbol *)
	    (* IMPORTANT: it means that Symbol ("_", Nofix)  as a special meaning !!!! *)
	    match s with
	      | Symbol ("_", Nofix) ->
		(* we only put brackets if implicit *)
		(if nature = Implicit then withBracket else fun x -> x)
		  (term2token ctxt ty (InArg nature))
	      | _ -> 
		(* here we put the nature marker *)
		(if nature = Implicit then withBracket else withParen)
		  (Box [Verbatim (symbol2string s); Space 1; Verbatim "::"; Space 1; term2token ctxt ty Alone])
	  in 
	  (* for computing the r.h.s, we need to push a new frame *)
	  let newframe = build_new_frame s (shift_term ty 1) in
	  let rhs = term2token (newframe::ctxt) te Alone in
	  Box [Verbatim "\\"; Space 1; lhs; Space 1; Verbatim "->"; Space 1; rhs]
	)

	(*
    | AVar _ -> raise (Failure "term2token - catastrophic: still an AVar in the term")
    | TName _ -> raise (Failure "term2token - catastrophic: still an TName in the term")
	*)
    | AVar _ -> Verbatim "_"
    | TName (s, _) -> Verbatim (symbol2string s)

and pattern2token (ctxt: context) (pattern: pattern) (p: place) : token =
  match pattern with
    | PType _ -> Verbatim "Type"
    | PVar (n, _, _) -> Verbatim n
    | PAVar _ -> Verbatim "_"
    | PCste (s, _) -> Verbatim (symbol2string s)
    | PAlias (n, pattern, _, _) -> Box [Verbatim n; Verbatim "@"; pattern2token ctxt pattern InAlias]

    (* for the append we have several implementation that mimics the ones for terms *)
    | PApp ((Symbol (s, Infix (myprio, myassoc)), _), args, _, _) when not !pp_option.show_implicit && List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 2->
      (* we should put parenthesis in the following condition: *)
      (match p with
	(* if we are an argument *)
	| InArg Explicit -> withParen
	(* if we are in a notation such that *)
	(* a prefix or postfix binding more  than us *)
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	(* or another infix with higher priority *)
	| InNotation (Infix (i, _), _) when i > myprio -> withParen
	(* or another infix with same priority depending on the associativity and position *)
	(* I am the first argument and its left associative *)
	| InNotation (Infix (i, LeftAssoc), 1) when i = myprio -> withParen
	(* I am the second argument and its right associative *)
	| InNotation (Infix (i, RightAssoc), 2) when i = myprio -> withParen
	(* if we are in an alias *)
	| InAlias -> withParen

	(* else we do not need parenthesis *)
	| _ -> fun x -> x
      ) (
	match (if !pp_option.show_implicit then List.map fst args else filter_explicit args) with
	  | arg1::arg2::[] ->
	    let arg1 = pattern2token ctxt arg1 (InNotation (Infix (myprio, myassoc), 1)) in
	    let arg2 = pattern2token ctxt arg2 (InNotation (Infix (myprio, myassoc), 2)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg1; te; arg2])
	  | _ -> raise (Failure "pattern2token, App infix case: irrefutable patten")
       )
    (* the case for Prefix *)
    | PApp ((Symbol (s, (Prefix myprio)), _), args, _, _) when not !pp_option.show_implicit && List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a postfix notation more binding than us
	 - in an alias
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InAlias -> withParen
	| InNotation (Postfix i, _) when i > myprio -> withParen
	| _ -> fun x -> x
      ) (
	match (if !pp_option.show_implicit then List.map fst args else filter_explicit args) with
	  | arg::[] ->
	    let arg = pattern2token ctxt arg (InNotation (Prefix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [te; arg])
	  | _ -> raise (Failure "pattern2token, App prefix case: irrefutable patten")
       )

    (* the case for Postfix *)
    | PApp ((Symbol (s, (Postfix myprio)), _), args, _, _) when not !pp_option.show_implicit && List.length (if !pp_option.show_implicit then List.map fst args else filter_explicit args) = 1 ->
      (* we put parenthesis when
	 - as the head or argument of an application
	 - in a prefix notation more binding than us
	 - in an alias
      *)
      (match p with
	| InArg Explicit -> withParen
	| InApp -> withParen
	| InNotation (Prefix i, _) when i > myprio -> withParen
	| InAlias -> withParen
	| _ -> fun x -> x
      ) (
	match (if !pp_option.show_implicit then List.map fst args else filter_explicit args) with
	  | arg::[] ->
	    let arg = pattern2token ctxt arg (InNotation (Postfix myprio, 1)) in
	    let te = Verbatim s in
	    Box (intercalate (Space 1) [arg; te])
	  | _ -> raise (Failure "term2token, App postfix case: irrefutable patten")
       )

    | PApp ((s, pos), args, _, _) when not !pp_option.show_implicit && List.length (filter_explicit args) = 0 ->
      term2token ctxt (Cste (s, pos)) p

    (* general case *)
    | PApp ((s, _), args, _, _) ->
      (* we only embed in parenthesis if
	 - we are an argument of an application
	 - we are in a notation (no !!! application more binding than operators)
      *)
      (match p with
	| InArg Explicit -> withParen
	| InAlias -> withParen
	| _ -> fun x -> x
      ) (
	let _, args = 
	  List.fold_left (
	    fun (ctxt, lst) te ->
	      input_pattern ctxt te, lst @ [pattern2token ctxt te (InArg Explicit)]
	  ) (ctxt, []) (if !pp_option.show_implicit then List.map fst args else filter_explicit args)
	in
	let s = symbol2string s in
	Box (intercalate (Space 1) (Verbatim s::args))
       )


(* make a string from a term *)
let term2string (ctxt: context) (te: term) : string =
  let token = term2token ctxt te Alone in
  let box = token2box token 80 2 in
  box2string box

let pattern2string (ctxt: context) (p: pattern) : string =
  let token = pattern2token ctxt p Alone in
  let box = token2box token 80 2 in
  box2string box

(* pretty printing for errors *)
let pos2token (p: pos) : token =
  match p with
    | ((-1, -1), (-1, -1)) -> Verbatim ""
    | (startp, endp) ->
      Box [Verbatim (string_of_int (fst startp)); 
	   Verbatim ":"; 
	   Verbatim (string_of_int (snd startp)); 
	   Verbatim "-"; 
	   Verbatim (string_of_int (fst endp)); 
	   Verbatim ":"; 
	   Verbatim (string_of_int (snd endp)); 
	  ]

    
let context2token (ctxt: context) : token =
  Box ([Verbatim "{"] 
       @ ( intercalates [Verbatim ";"; Newline]
	     (map_remain (fun hd tl ->
	       Box [Verbatim "(";
		    Verbatim (symbol2string hd.symbol); Space 1; Verbatim ":="; Space 1; term2token (hd::tl) hd.value Alone; Space 1; Verbatim "::"; Space 1; term2token (hd::tl) hd.ty Alone; Newline;
		    Box (intercalates [Verbatim ";"; Newline] (List.map (fun (i, ty, te) -> 
		      Box [Verbatim "(";
			   Verbatim (string_of_int i); Space 1; Verbatim "=>"; Space 1; term2token (hd::tl) te Alone; Space 1; Verbatim "::"; Space 1; term2token (hd::tl) ty Alone;
			   Verbatim ")"
			  ]
		    ) hd.fvs)
		    );
		    Verbatim ")"		    
		   ]
	      ) ctxt
	     )
       )	  
       @ [Verbatim "}"]
  )

let rec error2token (err: doudou_error) : token =
  match err with
    | NegativeIndexBVar i -> Verbatim "bvar as a negative index"
    | Unshiftable_term (te, level, delta) -> Verbatim "Cannot shift a term"
    | UnknownCste c -> Box [Verbatim "unknown constante:"; Space 1; Verbatim (symbol2string c)]

    | UnknownBVar (i, ctxt) -> Box [Verbatim "unknown bounded var:"; Space 1; Verbatim (string_of_int i); Space 1; context2token ctxt]
    | UnknownFVar (i, ctxt) -> Verbatim "UnknownFVar"

    | UnknownUnification (ctxt, te1, te2) | NoUnification (ctxt, te1, te2) ->
      Box [
	Verbatim "Cannot unify"; Newline;
	pos2token (get_term_pos te1); Space 1; term2token ctxt te1 Alone; Newline;
	pos2token (get_term_pos te2); Space 1; term2token ctxt te2 Alone; Newline
      ]
    | NoMatchingPattern (ctxt, p, te) ->
      Box [
	Verbatim "Cannot unify:"; Newline;	
	pos2token (get_pattern_pos p); Space 1; pattern2token ctxt p Alone; Newline;
	pos2token (get_term_pos te); Space 1; term2token ctxt te Alone;
      ]
    | CannotInfer (ctxt, te, err) ->
      Box [
	Verbatim "cannot infer type for:"; Space 1;
	pos2token (get_term_pos te); Space 1; term2token ctxt te Alone; Newline;
	Verbatim "reason:"; Newline;
	error2token err
      ]
    | CannotTypeCheck (ctxt, te, inferedty, ty, err) ->
      Box [
	Verbatim "the term:"; Space 1;
	pos2token (get_term_pos te); Space 1; term2token ctxt te Alone; Newline;
	Verbatim "of infered type:"; Space 1;
	term2token ctxt inferedty Alone; Newline;
	Verbatim "cannot be typecheck with type:"; Space 1;
	pos2token (get_term_pos ty); Space 1; term2token ctxt ty Alone; Newline;
	Verbatim "reason:"; Newline;
	error2token err
      ]
    | FreeError s -> Verbatim s
    | _ -> Verbatim "Internal error"

let equation2token (ctxt: context) (eq: equation) : token =
  let (p, te) = eq in
  Box [pattern2token ctxt p Alone; Space 1; Verbatim ":="; Space 1;
       let ctxt = input_pattern ctxt p in term2token ctxt te Alone]

let defs2token (defs: defs) : token =
  (* fold : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) t -> 'c -> 'c *)
  Box (
    Hashtbl.fold (fun key value acc ->
      match value with
	| (s, ty, _) ->
	  acc @ [Box [Verbatim (symbol2string s); Space 1; Verbatim "::"; Space 1; term2token [] ty Alone]; Newline]
    ) defs.store []
  )  

(* make a string from an error *)
let error2string (err: doudou_error) : string =
  let token = error2token err in
  let box = token2box token 80 2 in
  box2string box

let judgment2string (ctxt: context) (te: term) (ty: term) : string =
  let token = Box [Verbatim "|-"; Space 1; term2token ctxt te Alone; Space 1; Verbatim "::"; Space 1; term2token ctxt ty Alone] in
  let box = token2box token 80 2 in
  box2string box

let context2string (ctxt: context) : string =
  let token = context2token ctxt in
  let box = token2box token 80 2 in
  box2string box

let equation2string (ctxt: context) (eq: equation) : string =
  let token = equation2token ctxt eq in
  let box = token2box token 80 2 in
  box2string box

let defs2string (defs: defs) : string =
  let token = defs2token defs in
  let box = token2box token 80 2 in
  box2string box


(**********************************)
(* parser (lib/parser.ml version) *)
(**********************************)

let with_start_pos (startp: (int * int)) (p: 'a parsingrule) : 'a parsingrule =
  fun pb ->
    let curp = cur_pos pb in
    if (snd startp <= snd curp) then raise NoMatch;
    p pb

let with_pos (p: 'a parsingrule) : ('a * pos) parsingrule =
  fun pb ->
    let startp = cur_pos pb in
    let res = p pb in
    let endp = cur_pos pb in
    (res, (startp, endp))

let doudou_keywords = ["Type"; "::"; ":="; "->"]

open Str;;

let parse_reserved : unit parsingrule =
  foldp (List.map (fun x -> keyword x ()) doudou_keywords)

let name_parser : name parsingrule = applylexingrule (regexp "[a-zA-Z][a-zA-Z0-9]*", 
						      fun (s:string) -> 
							if List.mem s doudou_keywords then raise NoMatch else s
)

let parse_avar : unit parsingrule = applylexingrule (regexp "_", 
						     fun (s:string) -> ()
)

let parse_symbol_name (defs: defs) : symbol parsingrule =
  foldp (skipmap (fun s ->
    match s with
      | Name _ -> None
      | _ -> Some (tryrule (fun pb -> let () = word (symbol2string s) pb in s))
  ) defs.hist)

let parseint = applylexingrule (regexp "[0-9]+", fun (s:string) -> int_of_string s)
;;

let parseassoc : associativity parsingrule =
  foldp [
    tryrule (fun pb -> let () = whitespaces pb in 
		       let () = word "right" pb in 
		       let () = whitespaces pb in
		       RightAssoc
    );
    tryrule (fun pb -> let () = whitespaces pb in 
		       let () = word "left" pb in 
		       let () = whitespaces pb in
		       LeftAssoc
    );
    tryrule (fun pb -> let () = whitespaces pb in 
		       let () = word "no" pb in 
		       let () = whitespaces pb in
		       NoAssoc
    )
  ]


let parse_symbol_name_def : symbol parsingrule = 
  let symbols = ["\\+"; "\\*"; "\\["; "\\]";
		 "@"; "-"; ":"; "|"; "\\&"; "="; "~"; "\\\\"; "/"
		] in
  let format_symbols = String.concat "" ["\\("; 
					 String.concat "\\|" symbols;
					 "\\)*"
					] in
  let nofix = applylexingrule (regexp (String.concat "" ["\\["; format_symbols; "\\]"]), 
			       fun (s:string) -> String.sub s 1 (String.length s - 2)) in 
  let prefix = applylexingrule (regexp (String.concat "" ["\\["; format_symbols; ")"]), 
			       fun (s:string) -> String.sub s 1 (String.length s - 2)) in 
  let postfix = applylexingrule (regexp (String.concat "" ["("; format_symbols; "\\]"]), 
			       fun (s:string) -> String.sub s 1 (String.length s - 2)) in 
  let infix = applylexingrule (regexp (String.concat "" ["("; format_symbols; ")"]), 
			       fun (s:string) -> String.sub s 1 (String.length s - 2)) in 
  (* no fix *)
  tryrule (fun pb ->
    let () = whitespaces pb in
    let s = nofix pb in
    let () = whitespaces pb in
    Symbol (s, Nofix)
  )
  (* prefix *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let s = prefix pb in
    let () = whitespaces pb in
    (* we might have the priority *)
    match mayberule (fun pb -> 
      let () = word ":" pb in
      let () = whitespaces pb in
      let i = parseint pb in
      let () = whitespaces pb in
      i
    ) pb with
      | None -> Symbol (s, Prefix 0)
      | Some i -> Symbol (s, Prefix i)
  )
  (* infix *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let s = infix pb in
    let () = whitespaces pb in
    (* we might have the priority *)
    match mayberule (fun pb -> 
      let () = word ":" pb in
      let () = whitespaces pb in
      let a = parseassoc pb in
      let () = whitespaces pb in
      let () = word "," pb in
      let () = whitespaces pb in
      let i = parseint pb in
      let () = whitespaces pb in
      (a, i)
    ) pb with
      | None -> Symbol (s, Infix (0, NoAssoc))
      | Some (a, i) -> Symbol (s, Infix (i, a))	
  )
  (* postfix *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let s = postfix pb in
    let () = whitespaces pb in
    (* we might have the priority *)
    match mayberule (fun pb -> 
      let () = word ":" pb in
      let () = whitespaces pb in
      let i = parseint pb in
      let () = whitespaces pb in
      i
    ) pb with
      | None -> Symbol (s, Postfix 0)
      | Some i -> Symbol (s, Postfix i)
  )
  (* just a name *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let n = name_parser pb in
    let () = whitespaces pb in
    Name n
  )


let parse_symbol (defs: defs) : symbol parsingrule =
  fun pb -> 
    let res = fold_stop (fun () s ->
      try
	let () = tryrule (word (symbol2string s)) pb in
	Right s
      with
	| NoMatch -> Left ()
    ) () defs.hist in
    match res with
      | Left () -> raise NoMatch
      | Right s -> s
	

let create_opparser_term (defs: defs) (primary: term parsingrule) : term opparser =
  let res = { primary = primary;
	      prefixes = Hashtbl.create (List.length defs.hist);
	      infixes = Hashtbl.create (List.length defs.hist);
	      postfixes = Hashtbl.create (List.length defs.hist);
	      reserved = parse_reserved;
	    } in
  let _ = List.map (fun s -> 
    match s with
      | Name _ -> ()
      | Symbol (n, Nofix) -> ()
      | Symbol (n, Prefix i) -> Hashtbl.add res.prefixes n (i, fun pos te -> App (Cste (s, pos), [te, Explicit], (fst pos, snd (get_term_pos te))))
      | Symbol (n, Infix (i, a)) -> Hashtbl.add res.infixes n (i, a, fun pos te1 te2 -> App (Cste (s, pos), [te1, Explicit; te2, Explicit], (fst (get_term_pos te1), snd (get_term_pos te2))))
      | Symbol (n, Postfix i) -> Hashtbl.add res.postfixes n (i, fun pos te -> App (Cste (s, pos), [te, Explicit], (fst (get_term_pos te), snd pos)))
  ) defs.hist in
  res

let create_opparser_pattern (defs: defs) (primary: pattern parsingrule) : pattern opparser =
  let res = { primary = primary;
	      prefixes = Hashtbl.create (List.length defs.hist);
	      infixes = Hashtbl.create (List.length defs.hist);
	      postfixes = Hashtbl.create (List.length defs.hist);
	      reserved = parse_reserved;
	    } in
  let _ = List.map (fun s -> 
    match s with
      | Name _ -> ()
      | Symbol (n, Nofix) -> ()
      | Symbol (n, Prefix i) -> Hashtbl.add res.prefixes n (i, fun pos te -> PApp ((s, pos), [te, Explicit], AVar nopos, (fst pos, snd (get_pattern_pos te))))
      | Symbol (n, Infix (i, a)) -> Hashtbl.add res.infixes n (i, a, fun pos te1 te2 -> PApp ((s, pos), [te1, Explicit; te2, Explicit], AVar nopos, (fst (get_pattern_pos te1), snd (get_pattern_pos te2))))
      | Symbol (n, Postfix i) -> Hashtbl.add res.postfixes n (i, fun pos te -> PApp ((s, pos), [te, Explicit], AVar nopos, (fst (get_pattern_pos te), snd pos)))
  ) defs.hist in
  res

(* these are the whole term set 
   - term_lvlx "->" term
*)
let rec parse_term (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term = begin
  tryrule (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let (names, ty, nature) = parse_impl_lhs defs leftmost pb in
    let () = whitespaces pb in
    let () = word "->" pb in
    let () = whitespaces pb in
    let body = parse_term defs leftmost pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    set_term_pos (build_impl names ty nature body) (startpos, endpos)
  ) 
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let () = word "\\" pb in
    let () = whitespaces pb in
    let qs = many1 (parse_lambda_lhs defs leftmost) pb in
    let () = whitespaces pb in
    let () = word "->" pb in
    let () = whitespaces pb in
    let body = parse_term defs leftmost pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    set_term_pos (build_lambdas qs body) (startpos, endpos)
  ) 
  <|> parse_term_lvl0 defs leftmost
end pb

and parse_impl_lhs (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : ((symbol * pos) list * term * nature) = begin
  (* first case 
     with paren
  *)
  tryrule (paren (fun pb ->
    let names = many1 (fun pb ->
      let () = whitespaces pb in
      let startpos = cur_pos pb in
      let n = name_parser pb in
      let endpos = cur_pos pb in
      let () = whitespaces pb in
      n, (startpos, endpos)
    ) pb in
    let () = whitespaces pb in
    let () = word "::" pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    (List.map (fun (n, p) -> Name n, p) names, ty, Explicit)
   )
  )
  (* or the same but with bracket *)
  <|> tryrule (bracket (fun pb ->
    let names = many1 (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let n = name_parser pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    n, (startpos, endpos)
    ) pb in
    let () = whitespaces pb in
    let () = word "::" pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    (List.map (fun (n, p) -> Name n, p) names, ty, Implicit)
  )
  )
  (* or just a type -> anonymous arguments *)
  <|> (fun pb -> 
    let ty = parse_term_lvl0 defs leftmost pb in
    ([Symbol ("_", Nofix), nopos], ty, Explicit)        
  )
  <|> (fun pb -> 
    let ty = paren (parse_term_lvl0 defs leftmost) pb in
    ([Symbol ("_", Nofix), nopos], ty, Explicit)        
  )
  <|> (fun pb -> 
    let ty = bracket (parse_term_lvl0 defs leftmost) pb in
    ([Symbol ("_", Nofix), nopos], ty, Implicit)        
  )
end pb

and parse_lambda_lhs (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : ((symbol * pos) list * term * nature) = begin
  (* first case 
     with paren
  *)
  tryrule (paren (fun pb ->
    let names = many1 (fun pb ->
      let () = whitespaces pb in
      let startpos = cur_pos pb in
      let n = name_parser pb in
      let endpos = cur_pos pb in
      let () = whitespaces pb in
      n, (startpos, endpos)
    ) pb in
    let () = whitespaces pb in
    let () = word "::" pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    (List.map (fun (n, p) -> Name n, p) names, ty, Explicit)
   )
  )
  (* or the same but with bracket *)
  <|> tryrule (bracket (fun pb ->
    let names = many1 (fun pb ->
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let n = name_parser pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    n, (startpos, endpos)
    ) pb in
    let ty = match (mayberule (fun pb ->
      let () = whitespaces pb in
      let () = word "::" pb in
      let () = whitespaces pb in
      let ty = parse_term defs leftmost pb in
      ty
    ) pb) with
      | None -> AVar nopos
      | Some ty -> ty in
    (List.map (fun (n, p) -> Name n, p) names, ty, Implicit)
  )
  )
  <|> (fun pb -> 
    let () = whitespaces pb in
    let startpos = cur_pos pb in
    let n = name_parser pb in
    let endpos = cur_pos pb in
    let () = whitespaces pb in
    ([Name n, (startpos, endpos)], AVar nopos, Explicit)        
  )

end pb

(* this is operator-ed terms with term_lvl1 as primary
*)
and parse_term_lvl0 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term = begin
  let myp = create_opparser_term defs (parse_term_lvl1 defs leftmost) in
  opparse myp
end pb

(* this is term resulting for the application of term_lvl2 *)
and parse_term_lvl1 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term = begin
  fun pb -> 
    (* first we parse the application head *)
    let startpos = cur_pos pb in
    let head = parse_term_lvl2 defs leftmost pb in    
    let () = whitespaces pb in
    (* then we parse the arguments *)
    let args = separatedBy (
      fun pb ->
      parse_arguments defs leftmost pb
    ) whitespaces pb in
    let endpos = cur_pos pb in
    match args with
      | [] -> head
      | _ -> 
	App (head, args, (startpos, endpos))
end pb

(* arguments: term_lvl2 with possibly brackets *)
and parse_arguments (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : (term * nature) = begin
  (fun pb -> 
    let te = bracket (parse_term_lvl2 defs leftmost) pb in
    (te, Implicit)
  )
  <|> (fun pb -> 
    let te = parse_term_lvl2 defs leftmost pb in
    (te, Explicit)
  )
end pb

(* these are the most basic terms + top-level terms in parenthesis *)
and parse_term_lvl2 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : term = begin
  tryrule (fun pb -> 
    let () = whitespaces pb in
    let (), pos = with_pos (word "Type") pb in
    let () = whitespaces pb in
    Type pos
  ) 
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in
    let (), pos = with_pos parse_avar pb in
    let () =  whitespaces pb in
    AVar pos
  ) 
  <|> tryrule (fun pb -> 
    let () =  whitespaces pb in
    let s, pos = with_pos (parse_symbol_name defs) pb in
    let () =  whitespaces pb in    
    TName (s, pos)
  )
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let n, pos = with_pos name_parser pb in
    let () = whitespaces pb in
    TName (Name n, pos)
  )
  <|> (paren (parse_term defs leftmost))
end pb

and parse_pattern (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : pattern = begin
  let myp = create_opparser_pattern defs (parse_pattern_lvl1 defs leftmost) in
  opparse myp
end pb

and parse_pattern_lvl1 (defs: defs) (leftmost: (int * int)) : pattern parsingrule =
  tryrule (fun pb -> 
    (* first we parse the application head *)
    let s, pos = with_pos (parse_symbol defs) pb in    
    let () = whitespaces pb in
    (* then we parse the arguments *)
    let args = List.flatten (
      separatedBy (
	fun pb ->
	  parse_pattern_arguments defs leftmost pb
      ) whitespaces pb) in
    let endpos = cur_pos pb in
    match args with
      | [] -> PCste (s, pos)
      | _ -> PApp ((s, pos), args, AVar nopos, (fst pos, endpos))	  
  )
  <|> tryrule (parse_pattern_lvl2 defs leftmost)


and parse_pattern_arguments (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : (pattern * nature) list = begin
  tryrule (paren (fun pb ->
    let patterns = many1 (fun pb ->
      let () = whitespaces pb in
      let n = parse_pattern_lvl2 defs leftmost pb in
      let () = whitespaces pb in
      n
    ) pb in
    let () = whitespaces pb in
    let () = word "::" pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    List.map (fun p -> set_pattern_type p ty, Explicit) patterns
   )
  )
  (* or the same but with bracket *)
  <|> tryrule (bracket (fun pb ->
    let patterns = many1 (fun pb ->
    let () = whitespaces pb in
    let n =  parse_pattern_lvl2 defs leftmost pb in
    let () = whitespaces pb in
    n
    ) pb in
    let () = whitespaces pb in
    let () = word "::" pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    List.map (fun p -> set_pattern_type p ty, Implicit) patterns
  )
  )
  <|>(fun pb -> 
    let te = bracket (parse_pattern defs leftmost) pb in
    [te, Implicit]
  )
  <|>(fun pb -> 
    let te = paren (parse_pattern defs leftmost) pb in
    [te, Explicit]
  )
  <|> (fun pb -> 
    let te = parse_pattern_lvl2 defs leftmost pb in
    [te, Explicit]
  )
end pb
  
and parse_pattern_lvl2 (defs: defs) (leftmost: (int * int)) (pb: parserbuffer) : pattern = begin
  (fun pb -> 
    let () = whitespaces pb in
    let (), pos = with_pos (word "Type") pb in
    let () = whitespaces pb in
    PType pos
  ) 
  <|> (fun pb ->
    let () =  whitespaces pb in
    let (), pos = with_pos parse_avar pb in
    let () =  whitespaces pb in
    PAVar (AVar nopos, pos) 
  ) 
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in
    let s, pos = with_pos (parse_symbol defs) pb in
    let () =  whitespaces pb in
    PCste (s, pos)
  )
  <|> tryrule (fun pb ->
    let () =  whitespaces pb in
    let startpos = cur_pos pb in
    let name = name_parser pb in
    let () = word "@" pb in
    let p = parse_pattern defs leftmost pb in
    let endpos = cur_pos pb in
    PAlias (name, p, AVar nopos, (startpos, endpos))
  )
  <|> (fun pb -> 
    let () =  whitespaces pb in
    let name, pos = with_pos name_parser pb in
    let () =  whitespaces pb in    
    PVar (name, AVar nopos, pos)
  )
  <|> (paren (parse_pattern defs leftmost))
end pb

type definition = DefSignature of symbol * term
		  | DefEquation of pattern * term
		  | DefTerm of term

let rec parse_definition (defs: defs) (leftmost: int * int) : definition parsingrule =
  (* a signature *)
  tryrule (fun pb ->
    let () = whitespaces pb in
    let s = parse_symbol_name_def pb in
    let () = whitespaces pb in
    let () = word "::" pb in
    let () = whitespaces pb in
    let ty = parse_term defs leftmost pb in
    DefSignature (s, ty)
  )
  (* here we should have the Destructor parser *)
  <|> tryrule (fun pb ->
    let () = whitespaces pb in
    let p = parse_pattern defs leftmost pb in
    let () = whitespaces pb in
    let () = word ":=" pb in
    let () = whitespaces pb in
    let te = parse_term defs leftmost pb in
    DefEquation (p, te)
  )
  (* finally a free term *)
  <|> tryrule (fun pb ->
    DefTerm (parse_term defs leftmost pb)
  )
    

(*************************************************************)
(*      unification/reduction, type{checking/inference}      *)
(*************************************************************)

let debug = ref false

(*
  reduction of terms
  several strategy are possible:
  for beta reduction: Lazy or Eager
  possibility to have strong beta reduction
  delta: unfold destructors (replace cste with their destructors)
  iota: try to match destructors l.h.s
  deltaiotaweak: if after delta reduction (on head of app), a iota reduction fails, then the delta reduction is backtracked
  deltaiotaweak_armed: just a flag to tell the reduction function that it should raise a IotaReductionFailed
  zeta: compute the let bindings
  eta: not sure if needed

  all these different strategy are used for several cases: unification, typechecking, ...
  
*)

(* for now only eager is implemented !!!*)
type strategy = 
  | Lazy 
  | Eager

type reduction_strategy = {
  beta: strategy;
  betastrong: bool;
  delta: bool;
  iota: bool;
  deltaiotaweak: bool;
  deltaiotaweak_armed: bool;
  zeta: bool;
  eta: bool;
}

(* the default strategy for typechecking/unification/ ...*)
let unification_strat : reduction_strategy = {
  beta = Eager;
  betastrong = false;
  delta = true;
  iota = true;
  deltaiotaweak = false;
  deltaiotaweak_armed = false;
  zeta = true;
  eta = true;
}

(* a special exception for the reduction which 
   signals that an underlying iota reduction fails
*)
exception IotaReductionFailed

(* unification pattern to term *)
(*
  this is quite conservative:
  - we do not "reformat" application. so the unification is not modulo right associativity of applicatino
  - we ask for equality of symbol for constant, rather than looking for possible alias
*)
let rec unification_pattern_term (ctxt: context) (p: pattern) (te:term) : substitution =
  match p, te with
    | PType _, Type _-> IndexMap.empty
    | PVar (n, ty, _), te -> IndexMap.singleton 0 te
    | PAVar _, te -> IndexMap.empty
    | PCste (s1, _), Cste (s2, _) when s1 = s2 -> IndexMap.empty
    | PCste (s1, _), Cste (s2, _) when s1 <> s2 -> raise (DoudouException (NoMatchingPattern (ctxt, p, te)))
    | PAlias (n, p, ty, _), te ->
      (* grab the substitution *)
      let s = unification_pattern_term ctxt p te in
      (* shift it by one (for the n of the alias) *)
      let s = shift_substitution s 1 in
      (* we put in the substitution the shifting of te by |s| + 1 at index 0 *)
      IndexMap.add 0 te s
    (* for the application, we only accept same constante as head and same number of arguments 
       this is really conservatives .. we could implement the same mechanism as in subtitution_term_term
    *)
    | PApp ((s1, _), args1, ty, _), App (Cste (s2, _), args2, _) when List.length args1 = List.length args2 && s1 = s2 ->
      (* we unify arguments one by one (with proper shifting) *)
      List.fold_left (fun s ((arg1, n1), (arg2, n2)) -> 
	(* first we unify both args *)
	let s12 = unification_pattern_term ctxt arg1 arg2 in
	(* we need to shift the accumulator by the number of introduced free variable == caridnality of s12 *)
	IndexMap.fold (fun k value acc -> IndexMap.add (k + IndexMap.cardinal s12) value acc) s s12
      ) IndexMap.empty (List.combine args1 args2)

    | _ -> raise (DoudouException (NoMatchingPattern (ctxt, p, te)))

and unification_term_term (defs: defs) (ctxt: context ref) (te1: term) (te2: term) : term =
  if !debug then printf "unification: %s Vs %s\n" (term2string !ctxt te1) (term2string !ctxt te2);
  match te1, te2 with

    (* the error cases for AVar and TName *)
    | AVar _, _ -> raise (Failure "unification_term_term catastrophic: AVar in te1 ")
    | _, AVar _ -> raise (Failure "unification_term_term catastrophic: AVar in te2 ")
    | TName _, _ -> raise (Failure "unification_term_term catastrophic: TName in te1 ")
    | _, TName _ -> raise (Failure "unification_term_term catastrophic: TName in te2 ")


    (* the trivial cases for Type, Cste and Obj *)
    | Type p1, Type p2 -> Type (best_pos p1 p2)
    | Obj (o1, p1), Obj (o2, p2) when o1 = o2 -> Obj (o1, best_pos p1 p2)
    | Cste (c1, p1), Cste (c2, p2) when c1 = c2 -> Cste (c1, best_pos p1 p2)

    (* the trivial case for variable *)
    | TVar (i1, p1), TVar (i2, p2) when i1 = i2 -> TVar (i1, best_pos p1 p2)

    | TVar (i1, p1), TVar (i2, p2) when i1 < 0 && i2 < 0 -> 
      let imin = min i1 i2 in
      let imax = max i1 i2 in
      let s = IndexMap.singleton imin (TVar (imax, best_pos p1 p2)) in
      ctxt := context_substitution s (!ctxt);
      TVar (imax, best_pos p1 p2)

    (* in other cases, the frame contains the value for a given bound variable. If its not itself, we should unfold *)
    | TVar (i1, p1), _ when i1 >= 0 && set_term_pos (bvar_value !ctxt i1) nopos <> TVar (i1, nopos) ->
      let _ = unification_term_term defs ctxt (bvar_value !ctxt i1) te2 in
      TVar (i1, p1)

    | _, TVar (i2, p2) when i2 >= 0 && set_term_pos (bvar_value !ctxt i2) nopos <> TVar (i2, nopos) ->
      let _ = unification_term_term defs ctxt te1 (bvar_value !ctxt i2) in
      TVar (i2, p2)

    (* the case for free variables *)
    (* we need the free var to not be a free var of the term *)
    | TVar (i1, p1), _ when i1 < 0 && not (IndexSet.mem i1 (fv_term te2)) -> (
      let s = IndexMap.singleton i1 te2 in
      ctxt := context_substitution s (!ctxt);
      te2      
    )
    | _, TVar (i2, p2) when i2 < 0 && not (IndexSet.mem i2 (fv_term te1))->
      let s = IndexMap.singleton i2 te1 in
      ctxt := context_substitution s (!ctxt);
      te1

    (* cases for constantes *)
    | Cste (c1, pos), _ -> (
      match unfold_constante defs c1 with
	(* c1 is an inductive, a constructor or an axiom, we should have the strict equality with te2 *)
	| Inductive _ | Axiom | Constructor -> 
	  if set_term_pos (reduction defs ctxt unification_strat te2) nopos = Cste (c1, nopos) then
	    Cste (c1, pos)
	  else
	    raise (DoudouException (NoUnification (!ctxt, te1, te2)))
	(* if just one equation, we might want to unfold *)
	| Equation [PCste (c2, _), te] when c1 = c2 ->
	  unification_term_term defs ctxt te te2
	(* these case is impossible *)
	| Equation [PCste (c2, _), te] when c1 <> c2 ->
	  raise (Failure "Catastrophic: an equation for a constante has a different constante symbol")
	(* more than one equation ... we do not now *)
	| Equation _ ->
	  raise (DoudouException (UnknownUnification (!ctxt, te1, te2)))
    )

    | _, Cste (c2, pos) -> (
      match unfold_constante defs c2 with
	(* c1 is an inductive, a constructor or an axiom, we should have the strict equality with te2 *)
	| Inductive _ | Axiom | Constructor -> 
	  if set_term_pos (reduction defs ctxt unification_strat te1) nopos = Cste (c2, nopos) then
	    Cste (c2, pos)
	  else
	    raise (DoudouException (NoUnification (!ctxt, te1, te2)))
	(* if just one equation, we might want to unfold *)
	| Equation [PCste (c1, _), te] when c1 = c2 ->
	  unification_term_term defs ctxt te1 te 
	(* these case is impossible *)
	| Equation [PCste (c1, _), te] when c1 <> c2 ->
	  raise (Failure "Catastrophic: an equation for a constante has a different constante symbol")
	(* more than one equation ... we do not now *)
	| Equation _ ->
	  raise (DoudouException (UnknownUnification (!ctxt, te1, te2)))
    )

    (* the case of two application: with not the same arity *)
    | App (hd1, args1, p1), App (hd2, args2, p2) when List.length args1 <> List.length args2 ->
      (* first we try to change them such that they have the same number of arguments and try to match them *)
      let min_arity = min (List.length args1) (List.length args2) in
      let te1' = if List.length args1 = min_arity then te1 else (
	let pos1 = fst (get_term_pos hd1) in
	let largs1 = take (List.length args1 - min_arity) args1 in
	let largs2 = drop (List.length args1 - min_arity) args1 in
	let pos2 = snd (get_term_pos (fst (last largs1))) in
	let pos3 = snd (get_term_pos (fst (last largs2))) in
	  App (App (hd1, largs1, (pos1, pos2)), largs2, (pos1, pos3))
      ) in
      let te2' = if List.length args2 = min_arity then te2 else (
	let pos1 = fst (get_term_pos hd2) in
	let largs1 = take (List.length args2 - min_arity) args2 in
	let largs2 = drop (List.length args2 - min_arity) args2 in
	let pos2 = snd (get_term_pos (fst (last largs1))) in
	let pos3 = snd (get_term_pos (fst (last largs2))) in
	App (App (hd2, largs1, (pos1, pos2)), largs2, (pos1, pos3))
      ) in
      (* we save the current context somewhere to rollback *)
      let saved_ctxt = !ctxt in
      (try 
	 unification_term_term defs ctxt te1' te2' 
       with
	 (* apparently it does not work, so we try to reduce them *)
	 | DoudouException _ ->
	   (* restore the context *)
	   ctxt := saved_ctxt;
	   (* reducing them *)
	   let te1' = reduction defs ctxt unification_strat te1 in
	   let te2' = reduction defs ctxt unification_strat te2 in
	   (* if both are still the sames, we definitely do not know if they can be unify, else we try to unify the new terms *)
	   if te1 = te1' && te2 = te2' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1' te2'
      )
    (* the case of two application with same arity *)
    | App (hd1, args1, p1), App (hd2, args2, p2) when List.length args1 = List.length args2 ->
      (* first we save the context and try to unify all term component *)
      let saved_ctxt = !ctxt in
      (try
	 (* we need to push the arguments (through this we also verify that the nature matches ) *)
	 (* we build a list where arguments of te1 and te2 are alternate *)
	 let rev_arglist = List.fold_left (
	   fun acc ((arg1, n1), (arg2, n2)) ->
	     if n1 <> n2 then
	     (* if both nature are different -> no unification ! *)
	       raise (DoudouException (NoUnification (!ctxt, te1, te2)))
	     else  
	       arg2::arg1::acc
	 ) [] (List.combine args1 args2) in
	 let arglist = List.rev rev_arglist in
	 (* and we push this list *)
	 push_terms ctxt arglist;
	 (* first we unify the head of applications *)
	 let hd = unification_term_term defs ctxt hd1 hd2 in
	 (* then we unify all the arguments pair-wise, taking them from the list *)
	 let args = List.map (fun (_, n) ->
	   (* we grab the next argument for te1 and te2 in the context (and we know that their nature is equal to n) *)
	   let [arg1; arg2] = pop_terms ctxt 2 in
	   (* and we unify *)
	   let arg = unification_term_term defs ctxt arg1 arg2 in
	   (arg, n)
	 ) args1 in
	 (* finally we have our unified term ! *)
	 App (hd, args, best_pos p1 p2)

       with
	 (* apparently it does not work, so we try to reduce them *)
	 | DoudouException _ ->
	   (* restore the context *)
	   ctxt := saved_ctxt;
	   (* reducing them *)
	   let te1' = reduction defs ctxt unification_strat te1 in
	   let te2' = reduction defs ctxt unification_strat te2 in
	   (* if both are still the sames, we definitely do not know if they can be unify, else we try to unify the new terms *)
	   if te1 = te1' && te2 = te2' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1' te2'
      )	
    (* the cases where only one term is an Application: we should try to reduce it if possible, else we do not know! *)
    | App (hd1, args1, p1), _ ->
      let te1' = reduction defs ctxt unification_strat te1 in
      if te1 = te1' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1' te2
    | _, App (hd2, args2, p2) ->
      let te2' = reduction defs ctxt unification_strat te2 in
      if te2 = te2' then raise (DoudouException (UnknownUnification (!ctxt, te1, te2))) else unification_term_term defs ctxt te1 te2'

    (* the impl case: only works if both are impl *)
    | Impl ((s1, ty1, n1, pq1), te1, p1), Impl ((s2, ty2, n2, pq2), te2, p2) ->
      (* the symbol is not important, yet the nature is ! *)
      if n1 <> n2 then raise (DoudouException (NoUnification (!ctxt, te1, te2))) else
	(* we unify the types *)
	let ty = unification_term_term defs ctxt ty1 ty2 in
	(* we push a frame *)
	let frame = build_new_frame s1 (shift_term ty 1) in
	ctxt := frame::!ctxt;
	(* we need to substitute te1 and te2 with the context substitution (which might have been changed by unification of ty1 ty2) *)
	let s = context2substitution !ctxt in
	let te1 = term_substitution s te1 in
	let te2 = term_substitution s te2 in
	(* we unify *)
	let te = unification_term_term defs ctxt te1 te2 in
	(* we pop the frame *)
	ctxt := fst (pop_frame !ctxt);
	(* and we return the term *)
	Impl ((s1, ty, n1, pq1), te, p1)

    (* the Lambda case: only works if both are Lambda *)
    | Lambda ((s1, ty1, n1, pq1), te1, p1), Lambda ((s2, ty2, n2, pq2), te2, p2) ->
      (* the symbol is not important, yet the nature is ! *)
      if n1 <> n2 then raise (DoudouException (NoUnification (!ctxt, te1, te2))) else
	(* we unify the types *)
	let ty = unification_term_term defs ctxt ty1 ty2 in
	(* we push a frame *)
	let frame = build_new_frame s1 (shift_term ty 1) in
	ctxt := frame::!ctxt;
	(* we need to substitute te1 and te2 with the context substitution (which might have been changed by unification of ty1 ty2) *)
	let s = context2substitution !ctxt in
	let te1 = term_substitution s te1 in
	let te2 = term_substitution s te2 in
	(* we unify *)
	let te = unification_term_term defs ctxt te1 te2 in
	(* we pop the frame *)
	let [te] = flush_fvars ctxt [te] in
	ctxt := fst (pop_frame !ctxt);
	(* and we return the term *)
	Lambda ((s1, ty, n1, pq1), te, p1)

    (* for all the rest: I do not know ! *)
    | _ -> 
      raise (DoudouException (UnknownUnification (!ctxt, te1, te2)))

and reduction (defs: defs) (ctxt: context ref) (strat: reduction_strategy) (te: term) : term = 
  if !debug then printf "reduction: %s\n" (term2string !ctxt te);
  match te with

    | Type _ -> te
    (* without delta reduction we do unfold *)
    | Cste (c1, _) when not strat.delta -> te


    (* with delta reduction we unfold *)
    | Cste (c1, _) when strat.delta -> (
      match unfold_constante defs c1 with
	| Equation [PCste (c2, _), te] when c1 = c2 -> te
	| Equation [PCste (c2, _), te] when c1 <> c2 ->
	  raise (Failure "Catastrophic: an equation for a constante has a different constante symbol")
	| _ -> te
    )

    | Obj _ -> te

    (* for both free and bound variables we have their value in the context *)
    | TVar (i, _) when i >= 0 -> te
    | TVar (i, _) when i < 0 && set_term_pos (fvar_value !ctxt i) nopos <> TVar (i, nopos) -> fvar_value !ctxt i
    | TVar (i, _) when i < 0 -> te

    (* trivial error cases *) 
    | AVar _ -> raise (Failure "reduction catastrophic: AVar")
    | TName _ -> raise (Failure "reduction catastrophic: TName")

    (* Impl: we reduce the type, and the term only if betastrong *)
    | Impl ((s, ty, n, pq1), te, p1) -> 
      let ty = reduction defs ctxt strat ty in
      if strat.betastrong then (
	(* we push a frame *)
	let frame = build_new_frame s (shift_term ty 1) in
	ctxt := frame::!ctxt;
	(* we reduce the body *)
	let te = reduction defs ctxt strat te in
	(* we pop the frame *)
	ctxt := fst (pop_frame !ctxt);
	(* and we return the term *)
	Impl ((s, ty, n, pq1), te, p1)

      ) else Impl ((s, ty, n, pq1), te, p1)

    (* Lambda: we reduce the type, and the term only if betastrong *)
    | Lambda ((s, ty, n, pq), te, p) -> 
      let ty = reduction defs ctxt strat ty in
      if strat.betastrong then (
	(* we push a frame *)
	let frame = build_new_frame s (shift_term ty 1) in
	ctxt := frame::!ctxt;
	(* we reduce the body *)
	let te = reduction defs ctxt strat te in
	(* we pop the frame *)
	let [te] = flush_fvars ctxt [te] in
	ctxt := fst (pop_frame !ctxt);
	(* and we return the term *)
	Lambda ((s, ty, n, pq), te, p)

      ) else Lambda ((s, ty, n, pq), te, p)
    
    (* Application: the big part *)
    (* for no only Eager is implemented *)
    | App _ when strat.beta = Eager -> (

      (* we do a case analysis ... *)
      match te with

	| App (hd, [], _) ->
	  reduction defs ctxt strat hd

	| App (Lambda ((s, ty, n, p1), te, p), (hd, _)::tl, p2) -> (

	  let hd = reduction defs ctxt strat hd in
	  let te = shift_term (term_substitution (IndexMap.singleton 0 (shift_term hd 1)) te) (-1) in
	  match tl with
	    | [] -> reduction defs ctxt strat te
	    | _ -> reduction defs ctxt strat (App (te, tl, (fst (get_term_pos te), snd p2)))

	)

	| App (Obj (o, _), args, _) -> (
	  let args = List.map (fun (arg, n) -> reduction defs ctxt strat arg, n) args in
	  reduction defs ctxt strat (o#apply defs !ctxt args)
	)

	(* a first subcase for app: with a Cste as head *)
	(* in case of deltaiota weakness, we need to catch the IotaReductionFailed exception *) 
	| App (Cste (c1, pos), args, pos2) -> (
	  match unfold_constante defs c1 with
	    | Equation eqs -> (
	      (* we reduce the arguments *)
	      let args = List.map (fun (arg, n) -> reduction defs ctxt strat arg, n) args in
	      (* we try all the possible equations *)
	      let res = fold_stop (fun () (p, body) ->
	      (* we could check that n = argn, but it should have been already checked *)
	      (* can we unify the pattern ? *)
		try 
		  (* we need to cut arguments *)
		  let PApp (_, pargs, _, _) = p in
		  let neededargs = take (List.length pargs) args in
		  let surplusargs = drop (List.length pargs) args in
		  let r = unification_pattern_term !ctxt p (App (Cste (c1, pos), neededargs, nopos)) in
		  let te = term_substitution r body in
		  match surplusargs with
		    | [] -> Right te
		    | _ -> Right (App (te, surplusargs, (fst (get_term_pos te), snd (get_term_pos (fst (last surplusargs))))))
		with
		  | DoudouException (NoMatchingPattern (ctxt, p, te)) -> 
		    Left ()
	      ) () eqs in
	      match res with
		| Left () -> te
		| Right te -> reduction defs ctxt strat te
	    )
	    | _ -> App (Cste (c1, pos), List.map (fun (arg, n) -> reduction defs ctxt strat arg, n) args, pos2)
	)

	(* App is right associative ... *)
	| App (App (te1, args1, p1), arg2, p2) ->
	  reduction defs ctxt strat (App (te1, args1 @ arg2, (fst p1, snd p2)))

	| App (hd, args, p) ->
	  App (hd, List.map (fun (arg, n) -> reduction defs ctxt strat arg, n) args, p)

    )

(*
  helper function that detect if the number of explicit arguments
  N.B.: no modulo reduction ....
*)      
and nb_explicite_arguments (defs: defs) (ctxt: context ref) (te: term) : int =
  match reduction defs ctxt unification_strat te with
    | Impl ((_, _, Implicit, _), te, _) -> 1 + nb_explicite_arguments defs ctxt te
    | _ -> 0

and typecheck (defs: defs) (ctxt: context ref) (te: term) (ty: term) : term * term =
  if !debug then printf "typecheck: %s :: %s\n" (term2string !ctxt te) (term2string !ctxt ty);
  (* save the context *)
  let saved_ctxt = !ctxt in
  try (
  match te, ty with
    (* one basic rule, Type :: Type *)
    | Type p1, Type p2 -> Type p1 , Type p2

    (* here we should have the case for which you cannot rely on the inference *)
      
    (* the most basic typechecking strategy, 
       infer the type ty', typecheck it with Type (really needed ??) and unify with ty    
    *)
    | _, _ ->
      let te, ty' = typeinfer defs ctxt te in
      (* we try to detect if there is more implicite quantification in the infer type than the typechecked type *)
      if nb_explicite_arguments defs ctxt ty' > nb_explicite_arguments defs ctxt ty then (
	(* yes, we need to apply the term to a free variable *)
	let fvty = add_fvar ctxt (Type nopos) in
	let fvte = add_fvar ctxt (TVar (fvty, nopos)) in
	let te = App (te, [TVar (fvte, nopos), Implicit], nopos) in
	(* and we retypecheck *)
	typecheck defs ctxt te ty
      ) else (
	(* no: we typecheck normally *)
	push_terms ctxt [te];
	let ty = unification_term_term defs ctxt ty ty' in
	let [te] = pop_terms ctxt 1 in
	te, ty
      )
  ) with
    | DoudouException ((CannotTypeCheck _) as err) ->
      raise (DoudouException err)
    | DoudouException err ->
      ctxt := saved_ctxt;
      let te, inferedty = typeinfer defs ctxt te in
      raise (DoudouException (CannotTypeCheck (!ctxt, te, inferedty, ty, err)))
      
and typeinfer (defs: defs) (ctxt: context ref) (te: term) : term * term =
  (*printf "typecheck: %s :: ???\n" (term2string !ctxt te);*)
  (* save the context *)
  let saved_ctxt = !ctxt in
  try (
  match te with
    | Type _ -> te, Type nopos

    | Cste (c1, _) -> te, constante_type defs c1

    | Obj (o, _) -> te, o#get_type

    | TVar (i, _) when i >= 0 -> te, bvar_type !ctxt i
    | TVar (i, _) when i < 0 -> te, fvar_type !ctxt i

    | TName (s, pos) -> (
      (* we first look for a bound variable *)
      match bvar_lookup !ctxt s with
	| Some i -> 
	  let te = TVar (i, pos) in
	  let ty = bvar_type !ctxt i in
	  te, ty
	| None -> 
	  (* we look for a constante *)
	  let te = Cste (constante_symbol defs s, pos) in
	  let ty = constante_type defs s in
	  te, ty
    )

    | Impl ((s, ty, n, pq), te, p) -> 
      (* first let's be sure that ty :: Type *)
      let ty, _ = typecheck defs ctxt ty (Type nopos) in
      (* then we push the frame for s *)
      let frame = build_new_frame s (shift_term ty 1) in
      ctxt := frame::!ctxt;
      (* we typecheck te :: Type *)
      let te, ty' = typecheck defs ctxt te (Type nopos) in
      (* we pop the frame for s *)
      ctxt := fst (pop_frame !ctxt);
      (* and we returns the term with type Type *)
      Impl ((s, ty, n, pq), te, p), ty'

    | Lambda ((s, ty, n, pq), te, p) -> 
      (* first let's be sure that ty :: Type *)
      let ty, _ = typecheck defs ctxt ty (Type nopos) in
      (* then we push the frame for s *)
      let frame = build_new_frame s (shift_term ty 1) in
      ctxt := frame::!ctxt;
      (* we typeinfer te *)
      let te, tety = typeinfer defs ctxt te in
      (* we pop the frame for s *)
      let [te; tety] = flush_fvars ctxt [te; tety] in
      ctxt := fst (pop_frame !ctxt);
      (* and we returns the term with type Type *)
      Lambda ((s, ty, n, pq), te, p), Impl ((s, ty, n, nopos), tety, nopos)

    (* app will have another version in typecheck that might force more unification or creation of free variables *)
    | App (te, args, pos) -> 
      let te, ty = typeinfer defs ctxt te in
      (* we push the term te, and its type *)
      push_terms ctxt [te];
      push_terms ctxt [ty];
      (* ty is in the state *)
      let nb_args = fold_cont (fun nb_processed_args args ->
	(* first pop the type *)
	let [ty] = pop_terms ctxt 1 in
	(* ty is well typed ... we should be able to reduce it just in case *)
	let ty = (
	  match ty with
	    | Impl _ -> ty
	    | _ -> reduction defs ctxt unification_strat ty
	) in
	(* we should push the args with there nature ... *)
	let remaining_args, ty = (	  
	  match args, ty with
	    | [], _ -> raise (Failure "typeinfer of App: catastrophic, we have an empty list !!!")
	    (* lots of cases here *)
	    (* both nature are the same: this is our arguments *)
	    | (hd, n1)::tl, Impl ((s, ty, n2, pq), te, p) when n1 = n2 -> 
	      (* we push an image of the impl, so that we can grab a body which may have been changed by typechecking *)
	      push_terms ctxt [Impl ((s, ty, n2, pq), te, p)];
	      (* first let see if hd has the proper type *)
	      let hd, ty = typecheck defs ctxt hd ty in
	      (* we compute the type of the application:
		 we grab back from the term stack the te terms
		 we substitute the bound var 0 (s) by shifting of 1 of hd, and then reshift the whole term by - 1		 
	      *)
	      let [Impl (_, te, _)] = pop_terms ctxt 1 in
	      let ty = term_substitution (IndexMap.singleton 0 (shift_term hd 1)) te in
	      let ty = shift_term ty (-1) in
	      (* we push the arg and its nature *)
	      push_terms ctxt [hd];
	      push_nature ctxt n1;
	      (* and we returns the information *)
	      tl, ty
	    (* the argument is explicit, but the type want an implicit arguments: we add free variable *)
	    | (hd, Explicit)::tl, Impl ((s, ty, Implicit, _), te, _) -> 
	    (* we add a free variable of the proper type *)
	      let fv = add_fvar ctxt ty in
	      (* we compute the type of the application:
		 we substitute the bound var 0 (s) by the free variable, and then reshift the whole term by - 1
	      *)	      
	      let ty = term_substitution (IndexMap.singleton 0 (TVar (fv, nopos))) te in
	      let ty = shift_term ty (-1) in
	      
	      (* we push the arg and its nature *)
	      push_terms ctxt [TVar (fv, nopos)];
	      push_nature ctxt Implicit;
	      (* and we returns the information *)
	      args, ty
	    | (hd, n)::_, Impl ((s, ty, n2, _), te, _) -> 	      
	      let args = List.rev (map_nth (fun i ->
		let [arg] = pop_terms ctxt 1 in
		let n = pop_nature ctxt in
		(arg, n)
	      ) nb_processed_args) in
	      let [te] = pop_terms ctxt 1 in
	      raise (DoudouException (CannotInfer (!ctxt, App (te, args@[hd,n], (fst (get_term_pos te), snd (get_term_pos hd))), (FreeError "terms needs an Explicit argument, but receives an Implicit one"))))
	) in
	(* before returning we need to repush the (new) type *)
	push_terms ctxt [ty];
	(* and returns the information *)
	remaining_args, nb_processed_args + 1
      ) 0 args in
      (* we pop the ty *)
      let [ty] = pop_terms ctxt 1 in
      (* then we pop the arguments *)
      let args = List.rev (map_nth (fun i ->
	let [arg] = pop_terms ctxt 1 in
	let n = pop_nature ctxt in
	(arg, n)
      ) nb_args) in
      (* finally we pop the application head *)
      let [te] = pop_terms ctxt 1 in
      App (te, args, pos), ty
    
    (* for the AVar we introduce a free var of type, and a free var of this type *)
    | AVar pos -> 
      let fvty = add_fvar ctxt (Type nopos) in
      let fvte = add_fvar ctxt (TVar (fvty, nopos)) in
      TVar (fvte, pos), TVar (fvty, nopos)

  ) with
    | DoudouException ((CannotInfer _) as err) ->
      raise (DoudouException err)
    | DoudouException err ->
      ctxt := saved_ctxt;
      raise (DoudouException (CannotInfer (!ctxt, te, err)))

and typecheck_pattern (defs: defs) (ctxt: context ref) (p: pattern) (ty: term) : pattern * term * term =
  let p', pte, pty = typeinfer_pattern defs ctxt p in
  
  let ty' = shift_term ty (pattern_size p') in

  (* we try to detect if there is more implicite quantification in the infer type than the typechecked type *)
  if nb_explicite_arguments defs ctxt pty > nb_explicite_arguments defs ctxt ty then (
    (* we need to add enough implicit arguments *)
    let new_args = List.map (fun (s, _, _, _) -> PVar (symbol2string s, AVar nopos, nopos), Implicit) (take (nb_explicite_arguments defs ctxt pty - nb_explicite_arguments defs ctxt ty) (fst (destruct_impl pty))) in
    let p'' = match p with | PCste (s, spos) -> PApp ((s, spos), new_args, AVar nopos, nopos) in
    ctxt := drop (pattern_size p') !ctxt;
    typecheck_pattern defs ctxt p'' ty
  ) else (
    push_terms ctxt [pte];
    let ty = unification_term_term defs ctxt ty' pty in
    let [pte] = pop_terms ctxt 1 in
    p', pte, ty  
  )

and typeinfer_pattern (defs: defs) (ctxt: context ref) (p: pattern) : pattern * term * term =
  match p with
    | PApp ((s, spos), args, ty, pos) -> (
      let sty = constante_type defs s in
      let (appty, te_done, args_done) = fold_cont (fun (appty, te_done, args_done) args ->

	let appty = (
	  match appty with
	    | Impl _ -> appty
	    | _ -> reduction defs ctxt unification_strat appty
	) in

	match args, appty with
	  | (arg, n1)::tl, Impl ((_, ty, n2, _), _, _) when n1 = n2 ->	    	    

	    (* we typecheck the pattern *)
	    let (arg, argte, argty) = typecheck_pattern defs ctxt arg ty in
	    (* we compute the type after application of the term *)
	    let Impl ((_, _, _, _), te, _) = shift_term appty (pattern_size arg) in
	    let appty = term_substitution (context2substitution !ctxt) (shift_term (term_substitution (IndexMap.singleton 0 (shift_term argte 1)) te) (-1)) in
	    (* we compute the te_done at this level *)
	    let te_done = List.map (fun (te, n) -> term_substitution (context2substitution !ctxt) (shift_term te (pattern_size arg)), n) te_done in
	    tl, (appty, te_done @ [argte, n1], args_done @ [arg, n1])	
	  | (arg, Explicit)::tl, Impl ((s, _, Implicit, _), _, _) ->
	    (* we just add an implicit *)
	    (PVar (symbol2string s, AVar nopos, spos), Implicit)::args, (appty, te_done, args_done)
	  | _ ->
	    raise (Failure "bad case")
      ) (sty, [], []) args in

      let p = PApp ((s, spos), args_done, appty, pos) in

      let ty, _ = typecheck defs ctxt ty (Type nopos) in
      let appty = unification_term_term defs ctxt appty ty in

      p, App (Cste (s, spos), te_done, pos), appty
      
    )
    | PVar (n, ty, p) ->
      let fvty = add_fvar ctxt (Type nopos) in
      let fvte = add_fvar ctxt (TVar (fvty, nopos)) in
      ctxt := build_new_frame (Name n) ~value:(TVar (fvte, p)) (TVar (fvty, nopos)) :: !ctxt;      
      let ty, _ = typecheck defs ctxt ty (Type nopos) in 
      let ty = unification_term_term defs ctxt ty (TVar (fvty, nopos)) in
      PVar (n, ty, p), TVar (0, p), ty

    | PCste (s, p) ->
      PCste (s, p), Cste (s, p), constante_type defs s

    | PType p->
      PType p, Type p, Type nopos

    | PAVar (ty, p) ->
      let fvty = add_fvar ctxt (Type nopos) in
      let fvte = add_fvar ctxt (TVar (fvty, nopos)) in
      ctxt := build_new_frame (Symbol ("_", Nofix)) ~value:(TVar (fvte, p)) (TVar (fvty, nopos)) :: !ctxt;      
      let ty, _ = typecheck defs ctxt ty (Type nopos) in 
      let ty = unification_term_term defs ctxt ty (TVar (fvty, nopos)) in
      PAVar (ty, p), TVar (0, p), ty

    | PAlias (s, p, ty, pos) ->
      let p, pte, pty = typeinfer_pattern defs ctxt p in
      let pte = shift_term pte 1 in
      let pty = shift_term pty 1 in
      ctxt := build_new_frame (Name s) ~value:pte pty :: !ctxt;
      let ty, _ = typecheck defs ctxt ty (Type nopos) in 
      let ty = unification_term_term defs ctxt ty pty in
      PAlias (s, p, ty, pos), TVar (0, pos), ty


(* typechecking for destructors where type of l.h.s := type of r.h.s *)
and typecheck_equation (defs: defs) (ctxt: context ref) (lhs: pattern) (rhs: term) : pattern * term =
  (* we infer the pattern *)
  let lhs', lhste, lhsty = typeinfer_pattern defs ctxt lhs in
  (* close the value alias for pattern quantified variables *)
  close_context ctxt;
  (* and we typecheck the rhs *)
  let rhs, rhsty = typecheck defs ctxt rhs lhsty in
  ctxt := drop (pattern_size lhs') !ctxt;
  lhs', rhs

(* close a context with bvar valued to fvars *)
and close_context (ctxt: context ref) : unit =
  let s = List.fold_left (fun s frame ->
    let s = shift_substitution s 1 in
    match frame.value with
      | TVar (i, p) when i < 0 && not (IndexMap.mem i s) -> IndexMap.add i (TVar (0, p)) s
      | _ -> s

  ) IndexMap.empty (List.rev !ctxt) in
  ctxt := context_substitution s !ctxt

(******************************************)
(*        tests with parser               *)
(******************************************)

open Stream

let ctxt = ref empty_context

let defs = ref empty_defs

(* the strategy to cleanup types *)
let clean_term_strat : reduction_strategy = {
  beta = Eager;
  betastrong = true;
  delta = true;
  iota = true;
  deltaiotaweak = false;
  deltaiotaweak_armed = false;
  zeta = true;
  eta = true;
}

let process_definition (defs: defs ref) (ctxt: context ref) (s: string) : unit =
    (* we set the parser *)
    let lines = stream_of_string s in
    let pb = build_parserbuffer lines in
    let pos = cur_pos pb in
    (* we save the context and the defs *)
    let saved_ctxt = !ctxt in
    let saved_defs = !defs in
    try
      let def = parse_definition !defs pos pb in
      let _ = ( match def with
	| DefSignature (s, ty) ->

	  (* we typecheck the type against Type *)
	  let ty, _ = typecheck !defs ctxt ty (Type nopos) in	  
	  (* we flush the free vars so far *)
	  let [ty] = flush_fvars ctxt [ty] in
	  (* add to the defs *)
	  addAxiom defs s ty;
	  (* just print that everything is fine *)
	  printf "Defined: %s :: %s \n" (symbol2string s) (term2string !ctxt ty)

	| DefEquation (PCste (s, spos) as p, te) | DefEquation (PApp ((s, spos), _, _, _) as p, te) ->

	  let p, te = typecheck_equation !defs ctxt p te in
	  (* we flush the free vars so far *)
	  let [] = flush_fvars ctxt [] in
	  (* add to the defs *)
	  addEquation defs s (p, te);
	  (* just print that everything is fine *)
	  printf "Equation: %s \n" (equation2string !ctxt (p, te));
	    
	| DefTerm te ->
	  (* we infer the term type *)
	  let te, ty = typeinfer !defs ctxt te in
	  let te = reduction !defs ctxt clean_term_strat te in
	  let ty = reduction !defs ctxt clean_term_strat ty in
	  (* we flush the free vars so far *)
	  let [te; ty] = flush_fvars ctxt [te; ty] in
	  (* just print that everything is fine *)
	  printf "Term |- %s :: %s \n" (term2string !ctxt te) (term2string !ctxt ty)
      ) in
      assert (List.length !ctxt = 1)
    with
      | NoMatch -> 
	printf "parsing error: '%s'\n%s\n" (Buffer.contents pb.bufferstr) (errors2string pb);
	raise Pervasives.Exit
      | DoudouException err -> 
	(* we restore the context and defs *)
	ctxt := saved_ctxt;
	defs := saved_defs;
	printf "error:\n%s\n" (error2string err);
	raise Pervasives.Exit

