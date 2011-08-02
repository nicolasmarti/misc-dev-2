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

  Copyright (C) Nicolas Marti
*)

open Ast;;
open Pparser;;
open Printf;;
open Str;;
open Pprinter;;
open Termchecker;;
open Definition;;
open Varmap;;
open Varset;;
open Term;;
open Universe;;
open Astparser;;
open Commandparser;;
open Listext;;
open Term;;
open Reduction;;

let line_stream_of_channel channel =
  Stream.from
    (fun _ ->
       try Some (input_line channel) with End_of_file -> None)

let in_channel = open_in "test.m";;

let lines = line_stream_of_channel in_channel;;

let pb = build_parserbuffer lines;;

(*
let res = astParser pb;;
*)

let st = {
  qv = [];
  fv = [];
  univ_var = VarSet.empty;
  univ_constraint = [];
  term_storage = ([])::[];
  def = (DefLeaf VarMap.empty);
  oracles = [];
  coercion = [];
  tc_tree = [];
}
;;

let init () =
  st.qv <- [];
  st.fv <- [];
  st.term_storage <- ([])::[];
  st.tc_tree <- [];
;;

let exec_st (te: term) = {
  strat = Eager;
  beta = true;
  betastrong = true;
  delta = true;
  iota = true;
  deltaiotaweak = true;
  zeta = true;
  eta = true;
  mdef = st.def;
  aliasesi = (
    let fvs = fv te in
      FreeVarSet.fold (
	fun hd acc ->
	  min hd acc
      ) fvs (-1)
  );
  aliases = FreeVarMap.empty;
  ctxt = []
};;

(*
try (
  let show_univ = true in
  let res = pparser_parser astpparser pb in
    pprintast res;
    printf " :=\n";
    let (te, ty) = termcheck st (Left res) None in
      pprintterm te show_univ;    
      printf " :\n";
      pprintterm ty show_univ;    
      printf "(\n";
      pprintunivconstraints st.univ_constraint;
      printf "\n)\n";
      printf "->b\n";
      pprintterm (betared te st.def) show_univ;    
)
with
  | NoMatch ->
      pparser_error astpparser pb 
;;
*)

let proceed (x, te, ty, n) =  
  (*printf "proceed...\n";*)
  init ();
  let tyte = (
    match ty with
      | None -> None
      | Some ty -> Some (fst (termcheck st (Left ty) None))
  ) in    
    st.tc_tree <- [];
    try
      let (te, ty) = termcheck st (Left te) tyte in
      let b = termcheckres2token te ty st in
      let b = token2box b 4000000 0 in
	printf "-------------------\n";
	printbox b;
	flush stdout;
	let te2 = reduction (exec_st te) te in
	let b2 = termcheckres2token te2 ty st in
	let b2 = token2box b2 4000000 0 in
	printbox b2;
	printf "-------------------\n\n\n";
	flush stdout;
	st.def <- (
	  match insertpathdef (x::[]) (te2, ty, n) st.def with
	    | None -> st.def
	    | Some d -> d
	);
	(match st.tc_tree with
	   | (t::_)::_ ->
	       let b = token2box t 4000000 0 in
		 (*printbox b;*)
		 ()
	   | _ -> ()
	);
	(te2, ty)
    with
      | TermCheckFailure s ->
	  printf "failed typechecking:\n";
	  let t = (Verbatim "|-") :: (Space 1) ::
	    (let t = match pparser_pprinter astpparser te with
	       | None -> (Verbatim "???")
	       | Some t -> t 
	     in t)
	    :: (Space 1) :: (Verbatim ":") :: (Space 1) :: (let t = (match tyte with
								       | None -> (Verbatim "???")
								       | Some tyte -> let t = term2token tyte false [] in Box t)
							    in t) :: [] in
	  let b = token2box (Box t) 200 0 in
	    printbox b;
	    printf "error: %s\n\n" s;
	    (match st.tc_tree with
	       | (t::_)::_ ->
		   let b = token2box t 4000000 0 in
		     printbox b
	       | _ -> printf "no derivation tree...\n\n"
	    );
	    raise NoMatch


	   
;;


let show_univ = false
;;

let test () =
try (
  while true do 
    (match commandparser pb with
       | Definition (x, te, ty) -> let _ = proceed (x, te, ty, UnknownDef) in ()
       | Recursive (x, te, ty) -> let _ = proceed (x, te, ty, FunctionDef) in ()
       | Inductive (n, Ast.Ind (x, args', ity, constructor'), ty) ->
	   let (te, ty) = proceed (n, Ast.Ind (x, args', ity, constructor'), ty, TypeDef) in
	   let (Ind (x, l, ty, lcons)) = te in
	   let l = List.combine (List.map fst constructor') lcons in
	   let _ = List.fold_left (
	     fun acc hd ->
	       let te = Constr (acc, Cste n) in
		 init ();
		 let (te, ty) = termcheck st (Right te) None in		  
		   st.def <- (
		     match insertpathdef ((fst hd)::[]) (te, ty, DataDef) st.def with
		       | None -> st.def
		       | Some d -> d
		   ); (acc + 1)
	   ) 0 l in	    
	    ()
       | Expression body -> 
	   let _ = proceed ("it", body, None, UnknownDef) in
	     ()
	     
      
	   
    );
    done
)
with
  | NoMatch ->
      let l = definition2ext [] st.def in	  
	printf "-------------------------\nDefinitions:\n\n";	  
	List.fold_left (
	  
	  fun tl hd ->
	    let (name, (te, ty, nature)) = hd in
	      printf "%s := \n" name;
	      pprintterm te show_univ;
	      printf " : \n";
	      pprintterm ty show_univ;		
	      printf "\n\n";
	) () l; 
	printf "-------------------------\n\n"; flush stdout;	      
	
;;

test ();;

(*
let v = (Verbatim "caca");;
let f = Frac (v, list_of_n_elt v 5);;
let f2 = Frac (v, list_of_n_elt f 4);;
let b = token2box f2 400 0 in
let b1 = token2box f 400 0 in  
let b2 = token2box (Verbatim "|") 400 0 in  
let b3 = vertical_concat Center b2 (vertical_concat Center b2 b2) in
  printbox b1;
  printbox b3;
  printbox (horizontal_concat Top b1 b1);
  printbox (horizontal_concat Top b1 b3);
*)

