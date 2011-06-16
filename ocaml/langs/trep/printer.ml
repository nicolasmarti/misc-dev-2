open Pprinter;;
open Def;;

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

let rec term2token (te : term) =
  match te with
    | Var (_, n) -> Verbatim n

    | AVar -> Verbatim "_"

    | Alias (n, te) -> Box [Verbatim n; Verbatim "@"; term2token te]

    | App (hd, tl) -> Box (intercalate (List.map term2token (hd::tl)) (Space 1))

    | Let (r, binders, te) -> Box [Verbatim (if r then "let rec" else "let"); 
				   Space 1; 				      
				   Box (intercalates (List.map binder2token binders) [Verbatim ";"; Newline]); 
				   Verbatim "in"; 
				   Space 1; term2token te
				  ]

    | Lambda (patterns, te) -> Box (
	[Verbatim "\\"; Space 1]
	@ (intercalate (List.map term2token patterns) (Space 1))
	@ [Space 1; Verbatim "->"; Space 1; term2token te]			    
      )

    | Case (te, eqs) ->
	Box [Verbatim "case"; Space 1; term2token te; Space 1; Verbatim "of"; Newline;
	     Box (intercalate (List.map (fun eq -> Box [Verbatim "|"; Space 1; equation2token eq]) eqs 
			      ) Newline)
	    ]

    | Ifte (b, c1 ,c2) ->
	Box [Verbatim "if"; Space 1; term2token b; Space 1; Verbatim "then"; Space 1; term2token c1; Space 1; Verbatim "else"; Space 1; term2token c2]

    | SrcInfo (te, startp, stop) -> 
	if true then
	  term2token te
	else 
	  Box [Verbatim "@("; term2token te; Verbatim ")"]

    | Annotated (te, ty) -> term2token te
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
;;



let rec kind2token (k: kind) =
  match k with
    | KStar -> Verbatim "*"
    | KImpl (lhs, rhs) -> Box [Verbatim "("; kind2token lhs; Verbatim ")"; Space 1; Verbatim "->";  Space 1; Verbatim "("; kind2token rhs; Verbatim ")"]
;;

let rec mltype2token (ty: mltype) =
  match ty with
    | Unit -> Verbatim "Unit"
    | Int i -> Verbatim (String.concat "" ["i"; string_of_int i])
    | Double -> Verbatim "Double"
    | Float -> Verbatim "Float"
    | TyVar v -> Verbatim v
    | TyImpl -> Verbatim "(->)"
    | TyApp (lhs, rhs) -> Box ([Verbatim "("; mltype2token lhs; Space 1] @ 
				 List.concat 
				 (intercalate (List.map (fun x -> [Verbatim "("; mltype2token x; Verbatim ")"]) rhs) [Space 1]) @ [Verbatim ")"]
			      )
    | _ -> raise (Failure "mltype2token: constructor not yet supported")
;;
