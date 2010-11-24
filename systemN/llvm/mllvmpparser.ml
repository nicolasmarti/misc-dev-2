open Mllvm;;
open Parser;;
open Pprinter;;
open Varmap;;
open Str;;

(**********************************)

let int_lexingrule : int lexingrule = (regexp "[0-9]+", fun (s:string) -> int_of_string s)
;;

let int_parsingrule : int parsingrule = applylexingrule int_lexingrule
;;

(**********************************)

let rec llvmtype_pprinter (typeenv: llvmtype VarMap.t) (ty: llvmtype) : token =
  match ty with
    | TUnit -> Verbatim "()"
    | TInteger i -> Verbatim (String.concat "" ["i"; string_of_int i]) 
    | TFloat -> Verbatim "Float"
    | TDouble -> Verbatim "Double"
    | TQuad -> Verbatim "Quad"
    | TBool -> Verbatim "Bool"
    | TString -> Verbatim "String"
    | TVar v -> Verbatim v
    | TFct (args, retty) -> Box ([Verbatim "("] @ 
				   (List.concat ( Array.to_list(Array.mapi (fun i hd ->
									      (if i != 0 then 
										 [Verbatim ","; Space 1]
									       else
										 []) @ [llvmtype_pprinter typeenv hd]
									   ) args
							       )
						)
				   ) @ 
				   [Verbatim ")->"; Space 1; llvmtype_pprinter typeenv retty]
				)
    | TPtr ty -> Box [Verbatim "*"; Space 1; llvmtype_pprinter typeenv ty]
    | TTuple args -> Box ([Verbatim "("] @ 
			    (List.concat ( Array.to_list(Array.mapi (fun i hd ->
								       (if i != 0 then 
									  [Verbatim ","; Space 1]
									else
									  []) @ [llvmtype_pprinter typeenv hd]
								    ) args
							)
					 )
			    ) @ 
			    [Verbatim ")"]
			 )
    | TVector (n, ty) -> Box [Verbatim "<"; Verbatim (string_of_int n); Space 1; Verbatim "x"; Space 1; llvmtype_pprinter typeenv ty; Verbatim ">"]
    | TArray (n, ty) -> Box [Verbatim "["; Verbatim (string_of_int n); Space 1; Verbatim "x"; Space 1; llvmtype_pprinter typeenv ty; Verbatim "]"]
    | _ -> raise (Failure "llvmtpe_pprinter: case not yet implemented")
;;

(*
  let reserved = ["Float"; "Double"; "Quad"] in
  let ident : string lexingrule = (regexp "[a-zA-Z][a-zA-Z0-9]*", fun (s:string) -> s) in
  let varparser =  (spaces >> ((fun s -> s) |> ((notpl reserved) >>> (applylexingrule ident)))) in
*)

let rec llvmtype_parser : llvmtype parsingrule =
  fun pb -> (
    (tryrule ( (fun x -> x) |> spaces >> keyword "()" TUnit ))
    <|> (tryrule ((fun _ i -> TInteger i) |> (spaces >>> keyword "i" ()) >> int_parsingrule))
    <|> (tryrule ((fun x -> x) |> spaces >> keyword "Float" TFloat ))
    <|> (tryrule ( (fun x -> x) |> spaces >> keyword "Double" TDouble ))
    <|> (tryrule ( (fun x -> x) |> spaces >> keyword "Quad" TQuad ))
    <|> (tryrule ( (fun x -> x) |> spaces >> keyword "Bool" TBool ))
    <|> (tryrule ( (fun x -> x) |> spaces >> keyword "String" TString ))

    <|> (tryrule (fun pb ->
		    let _ = (spaces >>> (keyword "(" ())) pb in
		    let args = separatedBy llvmtype_parser (spaces >>> keyword "," ()) pb in
		    let _ = (spaces >>> (keyword ")->" ())) pb in
		    let retty = llvmtype_parser pb in
		      TFct (Array.of_list args, retty)
		 )
	)

    <|> (tryrule (fun pb ->
		    let _ = (spaces >>> (keyword "*" ())) pb in
		    let ty = llvmtype_parser pb in
		      TPtr ty
		 )
	)

    <|> (tryrule (fun pb ->
		    let _ = (spaces >>> (keyword "(" ())) pb in
		    let args = separatedBy llvmtype_parser (spaces >>> keyword "," ()) pb in
		    let _ = (spaces >>> (keyword ")" ())) pb in
		      match List.length args with
			| 0 -> TUnit
			| 1 -> List.hd args
			| _ -> TTuple (Array.of_list args)
		 )
	)

    <|> (tryrule (fun pb ->
		    let _ = (spaces >>> (keyword "<" ())) pb in
		    let n = (spaces >>> int_parsingrule) pb in
		    let _ = (spaces >>> (keyword "x" ())) pb in
		    let ty = llvmtype_parser pb in
		    let _ = (spaces >>> (keyword ">" ())) pb in
		      TVector (n, ty)
		 )
	)

    <|> (tryrule (fun pb ->
		    let _ = (spaces >>> (keyword "[" ())) pb in
		    let n = (spaces >>> int_parsingrule) pb in
		    let _ = (spaces >>> (keyword "x" ())) pb in
		    let ty = llvmtype_parser pb in
		    let _ = (spaces >>> (keyword "]" ())) pb in
		      TArray (n, ty)
		 )
	)

    <|> (tryrule ((let reserved = ["Float"; "Double"; "Quad"; "Bool"; "String"; "x"] in
		   let ident : string lexingrule = (regexp "[a-zA-Z][a-zA-Z0-9]*", fun (s:string) -> s) in
		   let varparser =  (spaces >> ((fun s -> s) |> ((notpl reserved) >>> (applylexingrule ident)))) in
		     (fun x -> TVar x) |> varparser)
		 )
	)
  ) pb
;;

(**********************************)
let rec cmd0_pprinter (te: cmd0) (paren: bool) : token =
  match te with
    | Unit -> Verbatim "()"
    | Return ty -> Box ([Verbatim "Return"; Space 1; cmd0_pprinter te true])
    | _ -> raise (Failure "cmd0_pprinter: case not yet implemented")
;;

let rec cmd0_parser : cmd0 parsingrule =
  fun pb -> (
    ( (fun x -> x) |> spaces >> keyword "()" Unit )
    (*<|> ( ( fun _ x -> Return x ) |> (spaces >>> keyword "return" ()) >> expr0_parser)*)
  ) pb
(*
and expr0_parser : expr0 parsingrule =
  raise (Failure "Not Yet Implemented: expr0 parser")
and cste_parser : cste parsingrule =
  raise (Failure "Not Yet Implemented: cste parser")
*)
;;
