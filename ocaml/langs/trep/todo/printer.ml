open Pprinter;;
open Trep;;

let rec intercalate l e =
  match l with
    | [] -> []
    | hd::[] -> hd::[]
    | hd1::hd2::tl-> hd1::e::(intercalate (hd2::tl) e)
;;

let rec intercalates l e =
  match l with
    | [] -> []
    | hd::[] -> hd::[]
    | hd1::hd2::tl-> hd1::e @ (intercalates (hd2::tl) e)
;;

let rec term2token (te : term) : token =
  match te with
    | Var (_, n) -> Verbatim n

    | AVar _ -> Verbatim "_"

    | App (hd, tl) -> Box (intercalate (term2token hd :: List.map arg2token (tl)) (Space 1))

    | Let (r, binders, te) -> Box [Verbatim (if r then "let rec" else "let"); 
				   Space 1; 				      
				   Box (intercalates (List.map binder2token binders) [Verbatim ";"; Newline]); 
				   Verbatim "in"; 
				   Space 1; term2token te
				  ]

    | Lambda (patterns, te) -> Box (
	[Verbatim "\\"; Space 1]
	@ (intercalate (List.map quantifier2token patterns) (Space 1))
	@ [Space 1; Verbatim "->"; Space 1; term2token te]			    
      )

    | Case (te, eqs) ->
	Box [Verbatim "case"; Space 1; term2token te; Space 1; Verbatim "of"; Newline;
	     Box (intercalate (List.map (fun eq -> Box [Verbatim "|"; Space 1; equation2token eq]) eqs 
			      ) Newline)
	    ]

    | Ifte (b, c1 ,c2) ->
	Box [Verbatim "if"; Space 1; term2token b; Space 1; Verbatim "then"; Space 1; term2token c1; Space 1; Verbatim "else"; Space 1; term2token c2]

    | SrcInfo (te, (startp, stop)) -> 
	if true then
	  term2token te
	else 
	  Box [Verbatim "@("; term2token te; Verbatim ")"]

    | TyAnnotation (te, ty) -> term2token te

    | _ -> raise (Failure "term2token: case not yet supported")

and binder2token (p, t) =
  Box [term2token p; Space 1; Verbatim ":="; Space 1; term2token t]
and equation2token eq =
  match eq with
    | NotGuarded (te1, te2) -> Box [term2token te1; Space 1; Verbatim ":="; Space 1; term2token te2]
    | Guarded (te1, gs) -> Box [term2token te1; Space 1; 
				Box (
				  intercalate (
				    List.map 
				      (fun (g, v) -> Box [Verbatim "with"; Space 1; term2token g; Space 1; Verbatim ":="; Space 1; term2token v; Newline])
				      gs
				  ) Newline
				)
			       ]
and arg2token arg =
  match arg with
    | (te, Explicit) -> Box [Verbatim "("; term2token te; Verbatim ")"]
    | (te, Implicit) -> Box [Verbatim "["; term2token te; Verbatim "]"]
    | (te, Hidden) -> Box [Verbatim "{"; term2token te; Verbatim "}"]

and quantifier2token q =
  let (ps, ty, n) = q in
  let (lf, rt) = 
    match q with
      | Hidden -> ("{", "}")
      | Explicit -> ("(", ")")
      | Implicit -> ("[", "]")
  in 
  Box ([Verbatim lt; term2token te; Verbatim ")"])
;;



