open Term;;
open Parser;;
open Pprinter;;
open Str;;
open Listext;;
open Env;;
open Universe;;
open Reduction;;
open Printf;;
open Unification;;
open Checker;;
open Definition;;

type symb = string * pos;;

type ast =
    
  (* the basic type Type *)
  | AType of pos

  | ASymb of symb

  (* basic quantification *)
  | ALet of symb * ast * ast 
  | ALambda of binders * ast
  | AForall of binders * ast

  (* Application *)
  | AApp of ast list

  | AOp of (string * int * associativity * pos) * ast * ast

  (* Destructor *)
  | AMatch of ast * (patterns * ast) list

  (* Anonymous variable , _*)
  | AAvar of pos option
and binder = (nature * (symb list) * ast)    
and binders = binder list   
and pattern = 
  | PSymb of symb
  | PAvar of pos
and patterns = pattern list      
;;

let nullpos = ((0, 0), (0, 0));;

(**********************)

(* Parser *)

let reserved = ["let"; "in"; "Type"; "V"; "match"; "with"; "returns"; "as"; "Inductive"; "Recursive"; "Definition"; "Compute"]
;;

(* TODO remove from ident all the keywords *)
let ident : string lexingrule = (regexp "[a-zA-Z][a-zA-Z0-9]*", fun (s:string) -> s)
;;

let commentrule : unit lexingrule = (regexp "(\\*\\(.\\|[' ' '\t' '\r' '\n']\\)*\\*)", fun (s:string) -> ()) 

type astparserstate = {
  binop_precedence: (string, (int * associativity * (pos -> ast -> ast -> ast))) Hashtbl.t
};;

let astparserstate_init () = {
  binop_precedence = Hashtbl.create 10
};;

let rec symb_parser (st: astparserstate) (pb: parserbuffer) : (string * pos) =
  (
    (spaces >> ((fun b s e -> (s, (b, e))) |> cur_pos >> ((notpl reserved) >>> (applylexingrule ident)) >> cur_pos)) 

    <|> (spaces >> ((fun hd -> hd) |> op_par_pos_parser st.binop_precedence)) 
  ) pb
and ast_parser (st: astparserstate) (pb: parserbuffer) : ast =
  (
    (
      (tryrule (operator_precedence (op_pos_parser st.binop_precedence) st.binop_precedence (ast_level2 st)))
    ) <!> "not an ast expression" 
  ) pb
and ast_level2 (st: astparserstate) (pb: parserbuffer) : ast =
  (
    (
      ((fun l -> (if List.length l = 1 then
		    List.nth l 0 
		  else
		    AApp l
		 )
       ) |> (many1 (ast_level1 st)))
    ) <!> "not an ast expression level1" 
  ) pb
and ast_level1 (st: astparserstate) (pb: parserbuffer) : ast =
      (tryrule ((fun _ x _ -> x) |>
		  (spaces >> (mayberule (applylexingrule commentrule))) >>
		  (ast_level0 st) >>
		  (spaces >> (mayberule (applylexingrule commentrule)))
	       )
       ) pb
and ast_level0 (st: astparserstate) (pb: parserbuffer) : ast =
  (
    (
      (tryrule (fun pb ->		    
		  let _ = keyword "let" () pb in
		  let s = symb_parser st pb in
		  let _ = keyword "=" () pb in
		  let a1 = ast_parser st pb in
		  let _ = keyword "in" () pb in
		  let a2 = ast_parser st pb in
		    ALet (s, a1, a2)		    
	       )
      )     
      <|> (tryrule (fun pb ->		    
		      let _ = keyword "\\" () pb in
		      let s = binders_parser_lambda st pb in
		      let _ = keyword "->" () pb in
		      let a1 = ast_parser st pb in
			ALambda (s, a1)		    
		   )
	  ) 
	<|> (tryrule (fun pb ->		    
			let _ = keyword "match" () pb in
			let a = ast_parser st pb in
			let _ = keyword "with" () pb in
			let ds = destructors_parser st pb in
			  AMatch (a, ds)		    
		     )
	    ) 
	<|> (tryrule (fun pb ->		    
			let s = binders_primary_parser_forall st pb in
			let _ = keyword "->" () pb in
			let a1 = ast_parser st pb in
			  AForall ([s], a1)		    
		     )
	    ) 
	  <|> (tryrule (fun pb ->
			  let _ = keyword "(" () pb in
			  let s = ast_parser st pb in
			  let _ = keyword ")" () pb in
			    s
		       )
	      )
	    <|> (tryrule ((spaces >> ((fun b s e -> AType (b, e)) |> cur_pos >> (applylexingrule (regexp_string "Type", (fun _ -> ()))) >> cur_pos))))
	      <|> (tryrule (
		     (fun x -> ASymb x) |> (symb_parser st)
		   )
		  )
		<|> (tryrule (
		       (fun x -> ASymb x) |> (op_par_pos_parser st.binop_precedence)
		     )
		    )
		<|> (tryrule ((spaces >> ((fun b s e -> AAvar (Some (b, e))) |> cur_pos >> (applylexingrule (regexp_string "_", (fun _ -> ()))) >> cur_pos))))
    ) <!> "not an ast expression level0"
  ) pb
and binders_parser_lambda (st: astparserstate) (pb: parserbuffer) : binders =
  let p = (tryrule (fun pb ->
		    let s = (symb_parser st) pb in
		      (Explicite, [s], AAvar None)
		 )	
	  ) in 
  (many1 ((binders_primary_parser_lambda st) <|> p)) pb
and binders_primary_parser_lambda (st: astparserstate) (pb: parserbuffer) : binder =
  (
    (tryrule (fun pb ->
		let _ = keyword "(" () pb in
		let s = many1 (symb_parser st) pb in
		let tyrule = ( fun pb ->
				 let _ = keyword ":" () pb in
				 let ty = ast_parser st pb in
				   ty
			     ) in
		let ty = (match mayberule tyrule pb with
			    | None -> AAvar None
			    | Some ty -> ty
			 ) in
		let _ = keyword ")" () pb in
		  (Explicite, s, ty)
     )
    )
    <|> (tryrule (fun pb ->
		    let _ = keyword "[" () pb in
		    let s = many1 (symb_parser st) pb in
		    let tyrule = ( fun pb ->
				     let _ = keyword ":" () pb in
				     let ty = ast_parser st pb in
				       ty
				 ) in
		    let ty = (match mayberule tyrule pb with
				| None -> AAvar None
				| Some ty -> ty
			     ) in
		    let _ = keyword "]" () pb in
		      (Implicite, s, ty)
		 )
	)
    <|> (tryrule (fun pb ->
		    let _ = keyword "{" () pb in
		    let s = many1 (symb_parser st) pb in
		    let tyrule = ( fun pb ->
				     let _ = keyword ":" () pb in
				     let ty = ast_parser st pb in
				       ty
				 ) in
		    let ty = (match mayberule tyrule pb with
				| None -> AAvar None
				| Some ty -> ty
			     ) in
		    let _ = keyword "}" () pb in
		      (Hidden, s, ty)
		 )
	)
      <!> "not a binder for lambda"
  ) pb
and binders_parser_forall (st: astparserstate) (pb: parserbuffer) : binders =
  let p = (tryrule (fun pb ->
		    let s = (symb_parser st) pb in
		      (Explicite, [("_", nullpos)], ASymb s)
		 )	
	  ) in 
  (many1 ((binders_primary_parser_forall st) <|> p)) pb
and args_parser (st: astparserstate) (pb: parserbuffer) : binders =
  let p = (tryrule (fun pb ->
		    let s = (symb_parser st) pb in
		      (Explicite, [("_", nullpos)], ASymb s)
		 )	
	  ) in 
  (many ((binders_primary_parser_forall st) <|> p)) pb
and binders_primary_parser_forall (st: astparserstate) (pb: parserbuffer) : binder =
  (
    (tryrule (fun pb ->
		let _ = keyword "(" () pb in
		let tyrule = ( fun pb ->
				 let s = many1 (symb_parser st) pb in
				 let _ = keyword ":" () pb in
				   s
			     ) in
		let s = (match mayberule tyrule pb with
			    | None -> [("_", nullpos)]
			    | Some s -> s
			 ) in
		let ty = ast_parser st pb in
		let _ = keyword ")" () pb in
		  (Explicite, s, ty)
     )
    )
    <|> (tryrule (fun pb ->
		let _ = keyword "{" () pb in
		let tyrule = ( fun pb ->
				 let s = many1 (symb_parser st) pb in
				 let _ = keyword ":" () pb in
				   s
			     ) in
		let s = (match mayberule tyrule pb with
			    | None -> [("_", nullpos)]
			    | Some s -> s
			 ) in
		let ty = ast_parser st pb in
		let _ = keyword "}" () pb in
		  (Hidden, s, ty)
     )
    )
    <|> (tryrule (fun pb ->
		let _ = keyword "[" () pb in
		let tyrule = ( fun pb ->
				 let s = many1 (symb_parser st) pb in
				 let _ = keyword ":" () pb in
				   s
			     ) in
		let s = (match mayberule tyrule pb with
			    | None -> [("_", nullpos)]
			    | Some s -> s
			 ) in
		let ty = ast_parser st pb in
		let _ = keyword "]" () pb in
		  (Implicite, s, ty)
     )
    )
    <!> "not a binder for forall"
  ) pb
and destructors_parser (st: astparserstate) (pb: parserbuffer) : (patterns * ast) list =
  (many
     (destructor_parser st
     )
  ) pb
and destructor_parser (st: astparserstate) (pb: parserbuffer) : (patterns * ast) =
  (
    (fun _ ps _ a -> (ps, a)) |>
	(keyword "|" ()) >>
	(patterns_parser st) >>
	(keyword "==>" ()) >>
	(ast_parser st)
  ) pb
and patterns_parser (st: astparserstate) (pb: parserbuffer) : patterns =
  (many1 
     (pattern_parser st
     )
  ) pb
and pattern_parser (st: astparserstate) (pb: parserbuffer) : pattern =
  (
    (tryrule ((spaces >> ((fun b s e -> PAvar (b, e)) |> cur_pos >> (applylexingrule (regexp_string "_", (fun _ -> ()))) >> cur_pos))))  
    <|> (tryrule ((fun s -> PSymb s) |> (symb_parser st)))
  ) pb
;;


(* still need definition and source parser *)

(**********************)

(* pprinting *)

let rec ast2token (a: ast) (b: bool) : token =
    match a with
      | AType p -> Box [Verbatim "Type"]
      | ASymb (s, p) -> Box [Verbatim s]
      | ALet ((s, p), t1, t2) ->
	  Box ((if b then [Verbatim "("] else []) @
		 [	    
		   Verbatim "let"; Space 1;
		   Verbatim "="; Space 1;
		   (ast2token t1 false); Space 1;
		   Verbatim "in"; Space 1;
		   (ast2token t2 false)
		 ] @ (if b then [Verbatim ")"] else [])
	      )
      | ALambda (bs, t) ->
	  Box ((if b then [Verbatim "("] else []) @
		 [
		   Verbatim "\\"; Space 1;
		   (binders2token bs [Space 1]); Space 1;
		   Verbatim "->"; Space 1;
		   (ast2token t false)
		 ] @ (if b then [Verbatim ")"] else [])
	      )
      | (AForall ([(Explicite, [("_", nullpos)], x)], t)) ->
	  Box ((if b then [Verbatim "("] else []) @
		 [(ast2token x true); Space 1;
		  Verbatim "->"; Space 1;
		  (ast2token t false)
		 ] @ (if b then [Verbatim ")"] else [])
	      )
      | (AForall ([(Hidden, [("_", nullpos)], x)], t)) ->
	  Box ((if b then [Verbatim "("] else []) @ 
		 [
		   Verbatim "{";(ast2token x false); Verbatim "}"; (Space 1);
		   Verbatim "->"; Space 1;
		   (ast2token t false)
		 ] @ (if b then [Verbatim ")"] else [])
	      )
      | (AForall ([(Implicite, [("_", nullpos)], x)], t)) ->
	  Box ((if b then [Verbatim "("] else []) @ 
		 [
		   Verbatim "["; (ast2token x false); Verbatim "]"; (Space 1);
		   Verbatim "->"; Space 1;
		   (ast2token t false)
		 ] @ (if b then [Verbatim ")"] else [])
	      )
      | AForall (bs, t) ->
	  Box ((if b then [Verbatim "("] else []) @ 
		 [
		   (binders2token bs [Space 1; Verbatim "->"; Space 1]); Space 1;
		   Verbatim "->"; Space 1;
		   (ast2token t false)
		 ] @ (if b then [Verbatim ")"] else [])
	      )
	    
      | AOp ((s, i, a, p), l, r) ->
	  let l' = (
	    match l with
	      | AOp ((_, i', _, _), _, _) -> (
		  if (i' < i)  || (i = i' && a = Parser.Right) then 
		    ast2token l true
		  else 
		    ast2token l false		
		)      		  
	      | _ -> ast2token l false
	  ) in
	  let r' = (
	    match r with
	      | AOp ((_, i', _, _), _, _) ->
		  if (i' < i)  || (i = i' && a = Parser.Left) then 
		    ast2token r true
		  else 
		    ast2token r false
	      | _ -> ast2token r false
	  ) in 
	    Box (
	      (if b then [Verbatim "("] else []) @ 
		([l'; Space 1; Verbatim s; Space 1; r'])
	      @ (if b then [Verbatim ")"] else [])
	    )
      | AApp l -> Box (intercalate (Space 1) $ List.map (fun hd -> 
							   let b =
							     match hd with
							       | ALet _ -> true
							       | ALambda _ -> true
							       | AForall _-> true
							       | AOp _ -> true
							       | AMatch _ -> true
							       | AApp _ -> true
							       | _ -> false

							   in
							     ast2token hd b) l)
      | AAvar p -> Verbatim "_"
      | AMatch (t, ds) ->
	  let t' = ast2token t false in
	  let ds' = destructors2token ds in
	    Box (
	      (if b then [Verbatim "("] else []) @ 
		([Verbatim "match"; Space 1; t'; Space 1; Verbatim "with"; Newline; ds'])
	      @ (if b then [Verbatim ")"] else [])
	    )
and binders2token (l: binders) i = 
  Box (
    intercalate (Box i) $ List.map binder2token l
  )
and binder2token (b: binder) = 
  let (n, vars, ty) = b in
  let (l, r) = (match n with
		  | Hidden -> ("{", "}")
		  | Explicite -> (match ty with
				    | AAvar p -> ("", "")
				    | _ -> ("(", ")")
				 )
		  | Implicite -> ("[", "]")
	       ) in
    Box ([Verbatim l] 
	 @ (intercalate (Space 1) $ List.map (fun hd -> Verbatim (fst hd)) vars)
	 @ (match ty with
	      | AAvar p -> [] 	   
	      | _ -> [Verbatim ":"; Space 1; ast2token ty false]
	   )
	 @ [Verbatim r]
	)
and destructors2token (l: (patterns * ast) list) = 
  Box (
    intercalate (Newline) $ List.map destructor2token l
  )
and destructor2token (d: (patterns * ast)) = 
  let (p, t) = d in
  let p' = patterns2token p in
  let t' = ast2token t false in
    Box [Verbatim "|"; Space 1; p'; Space 1; Verbatim "==>"; Space 1; t'; Newline]
and patterns2token (l: patterns) = 
  Box (
    intercalate (Space 1) $ List.map pattern2token l
  )
and pattern2token (p: pattern) = 
  match p with
    | PSymb (s, p) -> Verbatim s
    | PAvar _ -> Verbatim "_"
;;

(**********************)

(* ast2term *)

let rec ast2term (a: ast) (env: string list) (st: typechecker_state) : term =
    match a with
      | AType p -> (
	  let u = tcst_freshuniv st in
	    TType u
	)
      | ASymb (s, p) -> (try 
			   TVar (list_index s env 0)
			 with
			   | Failure s' ->
			       match finddef s st.def with
				 | None -> (
				     printf "%s not in:\n" s;
				     List.fold_left (
				       fun acc hd ->
					 printf "%s\n" hd
				     ) () env;
				     raise (Failure s')
				   )
				 | Some (n, (te, ty, nat)) -> (
				     TCste s
				   )
			)
      | ALet ((s, p), t1, t2) -> ( 
	  let u = tcst_freshuniv st in
	    TLet ((s, ast2term t1 env st, TType u), ast2term t2 (s::env) st)
	)
      | ALambda ([], t) -> ast2term t env st
      | ALambda ((n, ss, ty)::l, t) -> (
	  let (env, bs) = binders2term ((n, ss, ty)::l) env st in
	    List.fold_right (fun hd acc ->
			       TLambda (hd, acc) 
			    ) bs (ast2term t env st)
	)
      | AApp [] -> printf "gros problem \n"; raise (Failure "catastrophic")
      | AApp (hd::[]) -> ast2term hd env st
      | AApp (hd::tl) -> TApp (ast2term hd env st, List.map (fun x -> (ast2term x env st, Explicite)) tl)
      | AAvar p -> (
	  let fv = tcst_add_fv st in
	    TVar fv
	)
      | AForall ([], t) -> ast2term t env st
      | AForall ((n, ss, ty)::l, t) -> (
	  let (env, bs) = binders2term ((n, ss, ty)::l) env st in
	    List.fold_right (fun hd acc ->
			       TForall (hd, acc) 
			    ) bs (ast2term t env st)
	)
      | AOp ((s, i, a, p), l, r) -> 
	  ast2term (AApp [ASymb (String.concat "" ["("; s;")"], p); l; r]) env st

      | AMatch (t, ds) -> (
	  let t = ast2term t env st in
	  let fv = tcst_add_fv st in
	  let destr = Array.make (List.length ds) None in
	  let _ = List.map (
	    fun (pattern, term) ->
	      match pattern with
		| (PSymb (s, p))::args -> (
		    let i = (match reduction_checker st (TCste s) with
			       | TConstr (i, _) -> i
			       | _ -> raise (Failure (String.concat "\n" ["head of destructor: "; s; ", not a constructor"]))
			    ) in
		    let args = List.map (
		      fun hd ->
			match hd with
			  | PSymb s -> (Explicite, [s], AAvar None)
			  | PAvar p -> (Explicite, [("@", p)], AAvar None)
		    ) args in
		    let te = ALambda (args, term) in
		    let te = ast2term te env st in
		      destr.(i) <- Some te
		  )
		| _ -> raise (Failure (String.concat "\n" ["head of destructor cannot be _ or destructor cannot be empty"]))
	  ) ds in
	    TMatch (t, destr, TVar fv)
	)


and binders2term (l: binders) (env: string list) (st: typechecker_state) : (string list * (string * term * nature) list) = 
  List.fold_left (fun (env, bs) hd ->
		    let (env', bs') = binder2term hd env st in
		      (env', bs @ bs')
		 ) (env, []) l

and binder2term (b: binder) (env: string list) (st: typechecker_state) : (string list * (string * term * nature) list) = 
  let (n, ss, ty) = b in
  let lty = List.rev (List.fold_left (
			fun acc hd -> 
			  let last = List.hd acc in
			    (shift_var last 1)::acc
		      ) ([ast2term ty env st]) (List.tl ss)
		     ) in
  let bs = List.map (fun hd -> (fst (fst hd), snd hd, n)) (List.combine ss lty) in
  let env = ((List.rev (List.map fst ss)) @ env) in
    (env, bs)
;;

(*

first need env

*)

(**********************)

type definition =

  | Inductive of (symb * binders * ast option * (symb * ast) list)
  | Recursive of (symb * binders * ast option * ast)
  | Definition of (symb * binders * ast option * ast)

  | Compute of symb option * ast

  | Record of (symb * (symb * ast) list)

  | TypeClass
  | Instance

type source = 
  | Require of symb
  | DefinitionS of definition * pos
  | Doc of string * pos
  | Infix of string * associativity * int * pos
  | Expr of ast * pos
;;

let rec cmd_parser (st: astparserstate) (pb: parserbuffer) : definition =
  (
    (tryrule (((fun _ x args _ ty _ l _ -> Inductive (x, args, (Some ty), l))
		  |> 
		      (keyword "Inductive" ()) >>
		      (symb_parser st) >>
		      (args_parser st) >>
		      (keyword ":" ()) >> 
		      (ast_parser st) >> 
		      (keyword ":=" ()) >> 		      
		      (many (
			 (fun _ x _ t -> (x, t)) |>
			     (keyword "|" ()) >> 
			     (symb_parser st) >>
			     (keyword ":" ()) >> 
			     (ast_parser st)			     
		       )
		      ) >>
		      (keyword "." ())
		  )
		 )
	) 
    <|> (tryrule (((fun _ x args _ l _ -> Inductive (x, args, None, l))
		  |> 
		      (keyword "Inductive" ()) >>
		      (symb_parser st) >>
		      (args_parser st) >>
		      (keyword ":=" ()) >> 		      
		      (many (
			 (fun _ x _ t -> (x, t)) |>
			     (keyword "|" ()) >> 
			     (symb_parser st) >>
			     (keyword ":" ()) >> 
			     (ast_parser st)			     
		       )
		      ) >>
		      (keyword "." ())
		  )
		 )
	) 
    <|> (tryrule (((fun _ x args _ ty _ body _ -> Recursive (x, args, (Some ty), body))
		  |> 
		      (keyword "Recursive" ()) >>
		      (symb_parser st) >>
		      (args_parser st) >>
		      (keyword ":" ()) >> 
		      (ast_parser st) >> 
		      (keyword ":=" ()) >> 		      
		      (ast_parser st) >>
		      (keyword "." ())
		  )
		 )
	) 
    <|> (tryrule (((fun _ x args _ body _ -> Recursive (x, args, None, body))
		  |> 
		      (keyword "Recursive" ()) >>
		      (symb_parser st) >>
		      (args_parser st) >>
		      (keyword ":=" ()) >> 		      
		      (ast_parser st) >>
		      (keyword "." ())
		  )
		 )
	) 
    <|> (tryrule (((fun _ x args _ ty _ body _ -> Definition (x, args, (Some ty), body))
		  |> 
		      (keyword "Definition" ()) >>
		      (symb_parser st) >>
		      (args_parser st) >>
		      (keyword ":" ()) >> 
		      (ast_parser st) >> 
		      (keyword ":=" ()) >> 		      
		      (ast_parser st) >>
		      (keyword "." ())
		  )
		 )
	) 
    <|> (tryrule (((fun _ x args _ body _ -> Definition (x, args, None, body))
		  |> 
		      (keyword "Definition" ()) >>
		      (symb_parser st) >>
		      (args_parser st) >>
		      (keyword ":=" ()) >> 		      
		      (ast_parser st) >>
		      (keyword "." ())
		  )
		 )
	) 
    <|> (tryrule (((fun _ body _ -> Compute (None, body))
		  |> 
		      (keyword "Compute" ()) >>
		      (ast_parser st) >>
		      (keyword "." ())
		  )
		 )
	) 
    <|> (tryrule (((fun _ x _ body _ -> Compute (Some x, body))
		  |> 
		      (keyword "Compute" ()) >>
		      (symb_parser st) >>
		      (keyword "as" ()) >> 
		      (ast_parser st) >>
		      (keyword "." ())
		  )
		 )
	) 
  ) pb
;;

(**********************)

let rec build_inductive_term (x: symb) (args: binders) (ty: ast option) (lcons: (symb * ast) list) (env: string list) (st: typechecker_state) : (string * term * term) list =
  let name = fst x in
  let (env, bs) = binders2term args env st in
  let ty = (match ty with
	      | None -> (
		  let fv = tcst_add_fv st in
		    TVar fv
		)
	      | Some ty -> (
		  ast2term ty env st
		)
	   ) in
  let tty = List.fold_right (fun hd acc -> TForall (hd, acc)) bs ty in
  let (lconsname, lconsty) = List.split lcons in
  let env = (name::env) in
  let lconsty = List.map (fun hd -> ast2term hd env st) lconsty in    
  let term = (name, TInd (name, bs, ty, Array.of_list lconsty), tty) in
  let constructors = List.map (fun (i, (hd1, hd2)) -> (fst hd1, TConstr (i, TCste name), List.fold_right (fun hd acc -> TForall(hd, acc)) bs hd2)
			      ) 
    (List.combine (iota 0 (List.length lconsname - 1)) (List.combine lconsname lconsty)) in
    [term] @ constructors
;;

let rec build_recursive_term (x: symb) (args: binders) (ty: ast option) (body: ast) (env: string list) (st: typechecker_state) : (string * term * term) list =
  let name = fst x in
  let (env, bs) = binders2term args env st in
  let ty = (match ty with
	      | None -> (
		  let fv = tcst_add_fv st in
		    TVar fv
		)
	      | Some ty -> (
		  ast2term ty env st
		)
	   ) in
  let tty = List.fold_right (fun hd acc -> TForall (hd, acc)) bs ty in
  let env = (name::env) in
  let body = ast2term body env st in   
  let term = (name, TPhi (name, bs, ty, Nothing, body), tty) in
    [term] 
;;

let rec build_definition_term (x: symb) (args: binders) (ty: ast option) (body: ast) (env: string list) (st: typechecker_state) : (string * term * term) list =
  let name = fst x in
  let (env, bs) = binders2term args env st in
  let ty = (match ty with
	      | None -> (
		  let fv = tcst_add_fv st in
		    TVar fv
		)
	      | Some ty -> (
		  ast2term ty env st
		)
	   ) in
  let tty = List.fold_right (fun hd acc -> TForall (hd, acc)) bs ty in
  let body = ast2term body env st in   
  let tte = List.fold_right (fun hd acc -> TLambda (hd, acc)) bs body in
  let term = (name, tte, tty) in
    [term] 
;;


(**********************)

open Printf;;

let line_stream_of_channel channel =
  Stream.from
    (fun _ ->
       try Some (input_line channel) with End_of_file -> None)

let lines = line_stream_of_channel stdin;;
let pb = build_parserbuffer lines;;

let astpst = astparserstate_init ();;

Hashtbl.add astpst.binop_precedence "+" (10, Parser.Left, fun p x y -> AOp (("+", 10, Parser.Left, p), x, y));;

Hashtbl.add astpst.binop_precedence "*" (20, Parser.Left, fun p x y -> AOp (("*", 20, Parser.Left, p), x, y));;

Hashtbl.add astpst.binop_precedence "->" (0, Parser.Right, fun p x y -> AForall ([(Explicite, [("_", nullpos)], x)], y));;


let _ = 
  try 
    let st = empty_typechecker_st () in
    let c = ((fun x -> x) |> many (cmd_parser astpst)) pb in
    let _ = List.map (fun hd ->
			reinit_typechecker_st st;
			printf "-----------------------------\n\n";
			match hd with
			  | Inductive (x, args, ty, lcons) -> (
			      let res = (build_inductive_term x args ty lcons [] st) in
			      let _ = List.map (
				fun (hd1, hd2, hd3) ->
				  let (te, ty) = infer st hd2 in
				    (match insertdef hd1 (te, ty, TypeDef) st.def with
				       | None -> ()
				       | Some d -> st.def <- d
				    );
				    printbox (token2box (Box (term2token te false [])) 40 2);
				    printf ":\n";
				    printbox (token2box (Box (term2token ty false [])) 40 2);
				    printf "\n"
			      ) res in
				()
			    )
				  
			  | Definition (x, args, ty, body) -> (
			      let (hd1, hd2, hd3) = List.hd (build_definition_term x args ty body [] st) in
			      (*let (te, ty) = termcheck st hd2 hd3 in*)
			      let (te, ty) = infer st hd2 in
				(match insertdef hd1 (te, ty, FunctionDef) st.def with
				   | None -> ()
				   | Some d -> st.def <- d
				);
				printbox (token2box (Box (term2token te false [])) 40 2);
				printf ":\n";
				printbox (token2box (Box (term2token ty false [])) 40 2);
				printf "\n"
			    )
			  | Recursive (x, args, ty, body) -> (			      
			      let (hd1, hd2, hd3) = List.hd (build_recursive_term x args ty body [] st) in
				printbox (token2box (Box (term2token hd2 false [])) 40 2); printf ":\n";
			      (*let (te, ty) = termcheck st hd2 hd3 in*)
			      let (te, ty) = infer st hd2 in
				(match insertdef hd1 (te, ty, FunctionDef) st.def with
				   | None -> ()
				   | Some d -> st.def <- d
				);
				printbox (token2box (Box (term2token te false [])) 40 2);
				printf ":\n";
				printbox (token2box (Box (term2token ty false [])) 40 2);
				printf "\n"
			    )
			  | Compute _ -> (
			      printf "Compute\n"			      
			    )
		     ) c in
      ()
		  
  with
    | NoMatch -> 
	printf "error:%s\n\n" (markerror pb);
	
;;


printf "\n\n";;



