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
    | Type _ -> Verbatim "Type"

    | Var (_, n) -> Verbatim n

    | TyAnnotation (te, _) -> term2token te

    | SrcInfo (te, _) -> term2token te

    | _ -> raise (Failure "term2token: NYI")
;;
