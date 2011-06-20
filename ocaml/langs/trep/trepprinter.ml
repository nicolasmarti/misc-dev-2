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

let rec withParen (t: token) : token =
  Box [Verbatim "("; t; Verbatim ")"]



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

    | _ -> raise (Failure "term2token: NYI")

and arg2token arg =
  match arg with
    | (te, Explicit) -> Box [term2token te InArg]
    | (te, Implicit) -> Box [Verbatim "["; term2token te InAs; Verbatim "]"]
    | (te, Hidden) -> Box [Verbatim "{"; term2token te InAs; Verbatim "}"]

;;
