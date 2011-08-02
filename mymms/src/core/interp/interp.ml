(*
  This file is part of Mymms.

  Mymms is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  Mymms is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with Mymms.  If not, see <http://www.gnu.org/licenses/>.

  Copyright (C) 2008 Nicolas Marti
*)

open List;;
open Varset;;
open Varmap;;
open String;;
open Def;;
open Printer;;
open Definition;;
open Listext;;
open Printf;;
open Rewrite;;
open Term;;
open Alpha;;

type iterm =
    | ICste of name * nature
    | IObj of term pObj
    | IVar of int
    | ILambda of iterm
    | IClosure of (iterm list) * iterm
    | IPhi of var * (var * term) list * term * (int list) option * term
    | IInd of var * (var * term) list * term * term list
    | IApp of iterm * iterm list
    | IMatch of iterm * (iterm list) * term
    | ICons of int * term
    | IType
;;

let rec decomp_iapp t =
  match t with
    | IApp (t1, t2) -> (

	let (t3, t4) = decomp_iapp t1 in
	  (t3, t4 @ t2)
	
      )
    | _ -> (t, [])
;;

exception Translationterm2iterm of string

let rec term2iterm t vars def =
  match t with
    | Cste c -> (
	match finddef c def with
	  | None -> (*raise (Translationterm2iterm (concat "" ("Cannot translate Cste: " :: (string_of_term t VarMap.empty) ::[])))*)
	      ICste (c, UNKNOWN)
	  | Some (_ , (_, _, nature)) -> 
	      ICste (c, nature)
      )
    | Obj o -> IObj o
    | Var v -> (
	try
	  let n = list_index v vars 0 in
	    IVar n
	with
	  | _ -> raise (Translationterm2iterm (concat "" ("Cannot translate var: " :: v ::[])))
      )
    | Lambda (x, ty, te) -> (
	
	let vars =  x::vars in
	  ILambda (term2iterm te vars def)

      )
    | App (f, args) ->
	let f = term2iterm f vars def in
	let args = List.map (fun t -> term2iterm t vars def) args in
	  IApp (f, args)
    | Match (t, ldes, _, Some ind) -> (
	
	let t = term2iterm t vars def in
	let ldes = List.map (fun t -> term2iterm t vars def) ldes in
	  IMatch (t, ldes, ind)

      )
	
    | Cons (n, t) ->
	ICons (n,t)

    | Phi (x, la, ty, li, body) -> IPhi (x, la, ty, li, body)

    | Ind (x, la, ty, lcons) -> IInd (x, la, ty, lcons)

    | Let (x, te1, te2) ->
	let te2 = term2iterm (Lambda (x, Avar, te2)) vars def in
	let te1 = term2iterm te1 vars def in
	  IApp (te2, te1::[])

    | Type -> IType

    | _ -> 
	raise (Translationterm2iterm (concat "" ("Cannot translate : " :: (string_of_term t VarMap.empty) ::[])))
;;

exception Translationiterm2term

let rec iterm2term t depth vars env =
  try (
    match t with
      | ICste (c, _) -> Cste c
      | IObj o -> Obj o
      | IVar n -> (
	  try 
	    Var (List.nth vars n)
	  with
	    |  _ -> 
		 iterm2term (List.nth env (n - (List.length vars))) depth vars env
	)
      | ILambda t ->
	  Lambda (
	    (concat "" ("v" :: (string_of_int depth) :: [])),
	    Avar,
	    iterm2term t (depth + 1) ((String.concat "" ("v" :: (string_of_int depth) :: []))::vars) env
	  )

      | IApp (f, args) ->
	  let f = iterm2term f depth vars env in
	  let args = List.map (fun t -> iterm2term t depth vars env) args in
	    App (f, args)	
      | IMatch (t, ldes, _) ->
	let t = iterm2term t depth vars env in
	let ldes = List.map (fun t -> iterm2term t depth vars env) ldes in
	  Match (t, ldes, None, None)	
      | ICons (n, t) ->
	  Cons (n, t)
      | IInd (x, la, ty, lcons) -> Ind (x, la, ty, lcons)
      | IPhi (x, la, ty, li, body) -> Phi (x, la, ty, li, body)
      | IType -> Type
      | IClosure (env, t) ->
	  Lambda (
	    (concat "" ("v" :: (string_of_int depth) :: [])),
	    Avar,
	    iterm2term t (depth + 1) ((String.concat "" ("v" :: (string_of_int depth) :: []))::vars) env
	  )    
	    
  ) with
    | Failure s -> 
	raise (Translationiterm2term)
;;

exception Itermexec of string

let rec itermexec t env def =    
  (*printf "[%s] |- %s\n\n" (List.fold_left (fun acc hd -> concat "\n" (acc :: (string_of_term (iterm2term hd 0 [] env) VarMap.empty) ::[])) "" env) (string_of_term (iterm2term t 0 [] env) VarMap.empty);*)
  match t with
    | IApp (f, args) -> (
	match args with
	  | [] -> itermexec f env def
	  | hd :: [] -> (	      
	      match itermexec f env def with
		| IClosure (env', t) -> (
		    let v = itermexec hd env def in
		      itermexec t (v::env') def
		  )
		| te ->
		    let (te1, te2) = decomp_iapp te in
		    let las = (te2 @ hd :: []) in
		      match te1 with
			| (ICons (n,i)) -> 
			    let las = (te2 @ (itermexec hd env def)::[]) in
			      IApp (te1, las)
			| (IInd (x, la, ty, lcons)) ->
			    let las = (te2 @ (itermexec hd env def)::[]) in
			      IApp (te1, las)
			| ICste (c, nature) -> (
			    let las = (te2 @ (itermexec hd env def)::[]) in
			      if (nature == FUNCTION || nature == UNKNOWN) then (
				match finddef c def with
				  | None -> raise (Itermexec (concat "" ("Cannot unfold: " :: c :: [])))
				  | Some (n , (te, ty, nature)) -> 
				      itermexec (IApp ((term2iterm te [] def), las)) env def
			      )
			      else 
				IApp (te1, las)
			  )			    
			| IPhi (x, la, ty, li, body) ->
			    let mterm = Phi (x, la, ty, li, body) in
			    let te1 = (rewrite_term_var_term body x mterm) in
			    let te1 = (largs_lambdas te1 la) in
			    (*let te1 = alpha_term_vars te1 VarSet.empty in*)
			    let te1 = term2iterm te1 [] def in
			    let las = (te2 @ (itermexec hd env def)::[]) in
			      itermexec (IApp (te1, las)) env def
			| IObj o -> (
			    let (l, _) = decomp_foralls o#get_type in
			      if List.length las == List.length l then (
				let las = (te2 @ (itermexec hd env def)::[]) in
				let las = List.map (fun x -> iterm2term x 0 [] env) las in
				let res = o#exec las def in
				let res = term2iterm res [] def in
				let (te1, te2) = decomp_iapp res in			      
				  match te1 with
				    | IObj o2 -> 
					if (o#equal o2) then (
					  (*printf "stay\n\n";*)
					  res
					)
					else (
					  (*printf "continue(1)\n\n";*)
					  itermexec res env def
					)
				    | _ -> 
					(*printf "continue(2)\n\n";*)
					itermexec res env def
			      )
			      else (
				(*printf "not enough args\n\n";*)
				(IApp (te1, las))
			      )
			  )
			| _ -> raise (Itermexec "(1)")
	      )
	    | _ ->
		let hd = Listext.init args in 
		let tl = Listext.last args in
		  itermexec (IApp (IApp(f, hd), tl::[])) env def
	)
      | ILambda t ->
	  IClosure (env, t)
      | IVar n ->
	  List.nth env n	
      | IInd (x, la, ty, lcons) -> IInd (x, la, ty, lcons)
      | ICons (n, i) -> ICons (n, i)
      | IMatch (te, ldes, ind) -> (
 	  let te = itermexec te env def in
	  let (te1, te2) = decomp_iapp te in
	    match te1 with 
	      | ICons (n, i) ->
		  let des = List.nth ldes n in
		  let nte = IApp (des, te2) in
		    itermexec nte env def
	      | ICste (c, nature) -> (
		  if (nature == DATA || nature == UNKNOWN) then (
		    match finddef c def with
		      | None -> raise (Itermexec (concat "" ("Cannot unfold: " :: c :: [])))
		      | Some (n , (te, ty, nature)) -> 
			  itermexec (IMatch (IApp ((term2iterm te [] def), te2), ldes, ind)) env def
		  )
		  else 
		    IMatch (IApp (te1, te2), ldes, ind)
		)
	      | _ -> 
		  raise (Itermexec "(2)")
	)
      | IPhi (x, la, ty, li, body) ->
	  IPhi (x, la, ty, li, body)
      | ICste (c, nature) ->
	  ICste (c, nature)
      | IObj o ->
	  IObj o
      | IType -> IType
      | IClosure (env, t) -> IClosure (env, t)
;;
