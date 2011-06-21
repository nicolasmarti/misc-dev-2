open Pprinter;;
open Trep;;

open Planck;;
open Op_prec;;

let rec intercalate l e =
  match l with
    | [] -> []
    | hd::[] -> hd::[]
    | hd1::hd2::tl-> hd1::e::(intercalate (hd2::tl) e)
;;

let rec intercalates (l: 'a list) (e: 'a list) : 'a list =
  match l with
    | [] -> []
    | hd::[] -> hd::[]
    | hd1::hd2::tl-> hd1::e @ (intercalates (hd2::tl) e)
;;

type place = InNotation of op * int (*position*)
	     | InApp
	     | InArg
	     | InAs
	     | InAlias

let rec withParen (t: token) : token =
  Box [Verbatim "("; t; Verbatim ")"]

let rec withAccol (t: token) : token =
  Box [Verbatim "["; t; Verbatim "]"]

let rec withBracket (t: token) : token =
  Box [Verbatim "{"; t; Verbatim "}"]

let rec term2token (te : term) (p: place) : token =
  match te with
    | Type _ -> Verbatim "Type"

    | Var (_, n) -> Verbatim n

    | AVar _ -> Verbatim "_"

    | Cste (Symbol (s, _)) -> Verbatim (String.concat "" ["("; s; ")"])

    | Cste (Name n) -> Verbatim n

    | App (Cste (Symbol (name, ({kind = `Infix _; _} as op))), args) when List.length (List.filter (fun x -> snd x = Explicit) args) = 2 -> (
      let [arg1; arg2] = List.filter (fun x -> snd x = Explicit) args in
      (match p with
	| InArg  -> withParen
	| InNotation (op', _) when op'.prec > op.prec -> withParen
	| InNotation (op', 0) when op'.prec = op.prec && op'.kind = `Infix `Right -> withParen (* as an arguments to a notation with equal priority but with non natural associativity*)
	| InNotation (op', 1) when op'.prec = op.prec && op'.kind = `Infix `Left  -> withParen (* as an arguments to a notation with equal priority but with non natural associativity*)
	| InApp -> withParen
	| _ -> fun x -> x
      ) (Box [term2token (fst arg1) (InNotation (op, 0)); Space 1; Verbatim name; Space 1; term2token (fst arg2) (InNotation (op, 1))])

    )      

    | App (hd, tl) -> (

      (match p with
	| InArg -> withParen
	| _ -> fun x -> x	  
      ) (Box (intercalate ((term2token hd InApp) :: (List.map (fun x -> arg2token x) tl)) (Space 1)))

    )

    | Obj o -> o#pprint ()

    | TyAnnotation (te, _) -> term2token te p

    | SrcInfo (te, _) -> term2token te p

    | Let (r, binders, te) -> 
      (match p with
	| InArg -> withParen
	| _ -> fun x -> x	  
      ) (Box [Verbatim (if r then "let rec" else "let"); 
	      Space 1; 				      
	      Box (intercalates (List.map letdef2token binders) [Verbatim ";"; Space 1; Newline]); 
	      Verbatim "in"; Space 1; term2token te InAs
	     ]
       )

    | Case (te, eqs) ->
	Box [Verbatim "case"; Space 1; term2token te InAs; Space 1; Verbatim "of"; Newline;
	     Box (intercalate (List.map (fun eq -> Box [Verbatim "|"; Space 1; equation2token eq]) eqs 
	     ) Newline)
	    ]

    | Ifte (b, c1 ,c2) ->
	Box [Verbatim "if"; Space 1; term2token b InAs; Space 1; Verbatim "then"; Space 1; term2token c1 InAs; Space 1; Verbatim "else"; Space 1; term2token c2 InAs]

    | Lambda (quantifiers, te) -> (

      (match p with
	| InArg -> withParen
	| _ -> fun x -> x	  
      )

      (Box (
	[Verbatim "\\"; Space 1]
	@ (intercalate (List.map quantifier2token quantifiers) (Space 1))
	@ [Space 1; Verbatim "->"; Space 1; term2token te InAs]			    
      ))  

    )

    | Impl (quantifier, te) -> (

      (match p with
	| InArg -> withParen
	| _ -> fun x -> x	  
      )
      (Box [quantifier2token quantifier; Space 1; Verbatim "->"; Space 1; term2token te InAs])  
    )

and arg2token arg =
  match arg with
    | (te, Explicit) -> Box [term2token te InArg]
    | (te, Implicit) -> Box [Verbatim "["; term2token te InAs; Verbatim "]"]
    | (te, Hidden) -> Box [Verbatim "{"; term2token te InAs; Verbatim "}"]
and letdef2token (p, t) =
  Box [pattern2token p InAs; Space 1; Verbatim ":="; Space 1; term2token t InAs]
and equation2token eq =
  match eq with
    | NotGuarded (te1, te2) -> Box [pattern2token te1 InAs; Space 1; Verbatim ":="; Space 1; term2token te2 InAs]
    | Guarded (te1, gs) -> Box [pattern2token te1 InAs; Space 1; 
				Box (
				  intercalate (
				    List.map 
				      (fun (g, v) -> Box [Verbatim "with"; Space 1; term2token g InAs; Space 1; Verbatim ":="; Space 1; term2token v InAs; Newline])
				      gs
				  ) Newline
				)
			       ]
and quantifier2token q =
  match q with
    | (qs, annot, nat) ->  
      let encadr = (
	match nat with
	  | Explicit -> if List.length qs > 1 || annot != NoAnnotation then withParen else (fun x -> x)
	  | Hidden -> withBracket
	  | Implicit -> withAccol
      ) in
      let postfix = (
	match annot with
	  | NoAnnotation -> (fun x -> x)
	  | Annotated ty | Infered ty -> (fun x -> Box [x; Space 1; Verbatim "::"; Space 1; term2token ty InAs])
      ) in
      encadr (
	postfix (
	  Box (intercalates (List.map (fun hd -> pattern2token hd InArg) qs) [Space 1])
	)
      )
and pattern2token pat p = 
  match pat with
    | PType -> Verbatim "Type"
    | PVar n -> Verbatim n
    | PAVar -> Verbatim "_"
    | PCste (Symbol (s, _)) -> Verbatim (String.concat "" ["("; s; ")"])
    | PCste (Name n) -> Verbatim n

    | PApp (PCste (Symbol (name, ({kind = `Infix _; _} as op))), args) when List.length (List.filter (fun x -> snd x = Explicit) args) = 2 -> (
      let [arg1; arg2] = List.filter (fun x -> snd x = Explicit) args in
      (match p with
	| InArg | InApp | InAlias -> withParen
	| InNotation (op', _) when op'.prec > op.prec -> withParen
	| InNotation (op', 0) when op'.prec = op.prec && op'.kind = `Infix `Right -> withParen (* as an arguments to a notation with equal priority but with non natural associativity*)
	| InNotation (op', 1) when op'.prec = op.prec && op'.kind = `Infix `Left  -> withParen (* as an arguments to a notation with equal priority but with non natural associativity*)
	| _ -> fun x -> x
      ) (Box [pattern2token (fst arg1) (InNotation (op, 0)); Space 1; Verbatim name; Space 1; pattern2token (fst arg2) (InNotation (op, 1))])

    )      

    | PApp (hd, tl) -> (
      (match p with
	| InArg | InAlias -> withParen
	| _ -> fun x -> x	  
      ) (Box (intercalate ((pattern2token hd InApp) :: (List.map (fun x -> parg2token x) tl)) (Space 1)))
    )
    | PAlias (n, p) -> Box [Verbatim n; Verbatim "@"; pattern2token p InAlias]
and parg2token arg =
  match arg with
    | (te, Explicit) -> Box [pattern2token te InArg]
    | (te, Implicit) -> Box [Verbatim "["; pattern2token te InAs; Verbatim "]"]
    | (te, Hidden) -> Box [Verbatim "{"; pattern2token te InAs; Verbatim "}"]
and declaration2token (d: declaration) = 
  match d with
    | Signature (s, ty) -> (
      Box [
	(match s with
	  | Symbol (s, _) -> Verbatim (String.concat "" ["("; s; ")"])
	  | Name s -> Verbatim s
	); Space 1; Verbatim "::"; Space 1; term2token ty InAs
      ]
    )
    | Equation (eq, decls) -> (
      Box ([equation2token eq] @ 
	      if List.length decls > 0 then
		[Newline; ISpace 1; Verbatim "where"; Space 1;
		 Box (intercalate (List.map (fun decl -> declaration2token decl) decls) Newline)
		]
	      else []
      )
    )
    | Inductive (name, qs, ty, cons) -> (
      Box (
	[ Verbatim "inductive"; Space 1;
	  Verbatim name; Space 1]
	@ (intercalate (List.map quantifier2token qs) (Space 1))
	@ [Space (if List.length qs > 0 then 1 else 0); Verbatim "::"; Space 1; term2token ty InAs; Space 1; Verbatim ":="; Newline;
	   Box (intercalate (List.map (fun (s, ty) -> Box [Verbatim "|"; Space 1; 
							   (match s with
							     | Symbol (s, _) -> Verbatim (String.concat "" ["("; s; ")"])
							     | Name s -> Verbatim s
							   ); Space 1; Verbatim "::"; Space 1; term2token ty InAs
							  ]
	   ) cons
	   ) Newline)
	  ]	 
      )	
	
    )
    | _ -> raise (Failure "NYI")
;;
