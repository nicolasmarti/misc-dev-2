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

open Varset;;
open Varmap;;
open Def;;
open Listext;;
open Prooftree;;
open Tactic;;
open Term;;
open Termeq;;
open Printf;;
open Printer;;
open String;;
open Definition;;

type typechecker_state = {
  mutable def: definition; 
  mutable coercion: (term * term) list;
  mutable oracles:  (context -> term -> definition -> (term option)) VarMap.t;
  mutable overload: ((term * int) list) VarMap.t;
  mutable implicite: int VarMap.t;
};;

let empty_state () : typechecker_state = {
  
  def = DefNode VarMap.empty; 
  coercion = [];
  oracles = VarMap.empty;
  overload = VarMap.empty;
  implicite = VarMap.empty;

};;

let clean_state st =
  st.def <- DefNode VarMap.empty; 
  st.coercion <- [];
  st.oracles <- VarMap.empty;
  st.overload <- VarMap.empty;
  st.implicite <- VarMap.empty
;;


let add_def name te ty nature state st =
  match insertdef name (te, ty, nature) state.def with
    | None -> ()
    | Some def -> 
	st.def <- def
;;
  


let add_overload name te nbimplicite state st =
  try (

    let l = VarMap.find name state.overload in

      st.overload <- VarMap.add name ((te, nbimplicite)::l) (VarMap.remove name st.overload);

  ) with
    | _ -> 
        st.overload <- VarMap.add name ((te, nbimplicite)::[]) st.overload
;;

let add_implicite name nbimplicite state st =
  try (
    
    let _ = VarMap.find name state.implicite in
      
      ()
        
        
  ) with
    | _ -> 
        st.implicite <- VarMap.add name nbimplicite st.implicite
;;

let add_coercion te ty st state = 
  st.coercion <- (te, ty)::st.coercion

;;

let add_oracles name o st =
  try (
    
    let _ = VarMap.find name st.oracles in
      
      ()
        
        
  ) with
    | _ -> 
        st.oracles <- VarMap.add name o st.oracles
;;


(*********************)

exception Imcompatible_Def;;

let pushst2inst1 st1 st2 =
  (match mergedef st1.def st2.def with
     | None -> 
	 raise Imcompatible_Def
     | Some def ->
	 st1.def <- def
  );
  st1.coercion <- st2.coercion @ st1.coercion;
  st1.oracles <- varmap_union st2.oracles st1.oracles;
  st1.implicite <- varmap_union st1.implicite st2.implicite;

  (
    VarMap.fold (

      fun key value acc ->

	List.fold_left (
	  
	  fun acc hd ->

	    let (te, nbimplicite) = hd in
	      add_overload key te nbimplicite st1 st1

	) () value

    ) st2.overload ()

  );    

;;


let popst2inst1 st1 st2 =
  (match diffdef st1.def st2.def with
     | None -> 
	 raise Imcompatible_Def
     | Some def ->
	 st1.def <- def
  );
  st1.coercion <- nth_tail (List.length st2.coercion) st1.coercion;
  st1.oracles <- varmap_diff st1.oracles st2.oracles;
  st1.implicite <- varmap_diff st1.implicite st2.implicite;
  
  VarSet.fold (
  
    fun name acc  ->

    try (
      
      let (l1, l2) = (VarMap.find name st1.overload, VarMap.find name st2.overload) in
	
	st1.overload <- VarMap.add name (nth_tail (List.length l2) l1) (VarMap.remove name st1.overload);
	
    ) with
      | _ -> 
          ()
	    
  ) (vmdomain st2.overload) () 

;;


type histInfo =
  | HistDef
  | HistInfo
  | HistLemma of name
  | HistTactic of tactics
  | HistRequired
  | HistOpen
  | HistClose of name
  | HistVariable
;;

type mymms_state = {
  mutable variable: name list;
  mutable tpck: typechecker_state; 
  mutable defhist: typechecker_state list;
  mutable prooftree : proof_tree list;
  mutable proof : tactics list;
  mutable subgoals: int;
  mutable hist: histInfo list;
  mutable required: name list list;
  mutable path: string list;
};;

let state : mymms_state = {
  
  variable = [];
  tpck = empty_state (); 
  defhist = [];
  prooftree = [];
  proof = [];
  subgoals = 0;
  hist = [];
  required = [];
  path = "Current"::[]

};;

let load_state = empty_state ()
;;

(*********************)
let oracleslist = varmap_vallist
;;

