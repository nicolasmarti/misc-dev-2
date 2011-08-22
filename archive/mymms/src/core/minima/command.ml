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

#include "../../../config"

open Printf;;
open Def;;
open List;;
open String;;
open Listext;;
open Varset;;
open Varmap;;
open Printer;;
open Rewrite;;
open Term;;
open Fold;;
open Kernel;;
open Tactic;;
open Indprinc;;
open State;;
open Termeq;;
open Simpl;;
open Show;;
open Definition;;
open Sys;;
open Unfold;;
open Dynlink;;
open Alpha;;

open Output;;

#ifdef LLVM
open Llvm;;
open Jitinit;;
open Compile;;
open Llvm_executionengine;;
#endif

open Interp;;
open Vm;;

(***************)
(* Definitions *)
(***************)

type definition =
  | Inductive of (name * (name * term) list * term * (name * term) list)
  | MutualInductive of (name * (name * term) list * term * (name * term) list) list
  | Definition of (name * term * term option)
  | Recursive of (name * (name * term) list * (int list) option * term * term)
  | MutualRecursive of (name * (name * term) list * (int list) option * term * term) list
;;

let rec definition2state def state path =
  match def with
    | Inductive (x, la, ty, lc) -> (

	let te = Ind (x, la, ty, list_proj2 lc) in 
	  (*printf "Inductive:= %s\n\n" (string_of_term te state.implicite);*)
	  match check_term path te None state.def state.coercion (oracleslist state.oracles) state.overload state.implicite with
            | None -> print_error (sprintf "Probleme: %s\n\n" (string_of_term te state.implicite)); None
            | Some (te, ty) ->
		match te with
		  | Ind (x2, la2, ty2, lc2) -> (

		      let def = VarMap.add x2 (te, ty, TYPE) VarMap.empty in
                        
		      let (lc3, def,_) = 
                        List.fold_left (
			  
			  fun l hd ->
			    let (lcmd, def, n) = l in
			    let (cname, ctype) = hd in
			      (lcmd @ cname::[],
                               (VarMap.add 
				  cname 
				  (Cons (n,Cste x2), (largs_foralls (var2cste_implicite (List.nth lc2 n) (mkdefinitionfromdef path def) state.overload state.implicite) la2), DATA) 
				  def
			       ),n+1)
                                
                                
                        ) (x2::[], def, 0) lc in
		      let ipty = ind_princ_type x2 la2 ty2 lc2 (DefLeaf def) in
		      let ipte = ind_princ_pf x2 la2 ty2 lc2 (DefLeaf def) in

			match mergedef state.def (mkdefinitionfromdef path def) with
			  | None -> None
			  | Some mdef ->
			      let (lc2, def) = (
				match check_term path ipte (Some ipty) mdef state.coercion (oracleslist state.oracles) state.overload state.implicite with
				  | None -> (lc3, def)
				  | Some (te, ty) ->
				      let name = concat "" (x2 :: "induc" :: []) in
					(name :: lc3, VarMap.add name (fold te VarSet.empty mdef, fold ty VarSet.empty mdef, TYPE) def)
			      ) in
				Some def
                          
                          
		    )
		  | _ -> print_error (sprintf "Probleme: %s\n\n" (string_of_term te state.implicite)); None
		      
      )

    | Definition (x, te, ty) -> (
	
	match check_term path te ty state.def state.coercion (oracleslist state.oracles) state.overload state.implicite with
	  | None -> None
	  | Some (te, ty) ->
              let def = VarMap.add x (te, ty, term_nature te state.def) VarMap.empty in
		Some def
      )

    | Recursive (x, la, ldec, ty, te) -> (
	
	let te = Phi (x, la, ty, ldec, te) in 
	  (*printf "Recursive:= %s\n\n" (string_of_term te state.implicite);*)
	  match check_term path te None state.def state.coercion (oracleslist state.oracles) state.overload state.implicite with
            | None -> None
            | Some (te, ty) ->
		
		let def = VarMap.add x (te, ty, FUNCTION) VarMap.empty in
		  Some def

      )

    | MutualInductive lind -> (

	(* (name * (name * term) list * term * (name * term) list) list *)

	let (name, terms, lnc) =
	  
	  List.fold_left (

	    fun acc hd ->
	      
	      let (x, la, ty, lc) = hd in
	      let (name, terms, lnc) = acc in
		
		let te = Ind (x, la, ty, list_proj2 lc) in 
		  		  
		  (name @ x::[], terms @ te :: [], lnc @ (list_proj1 lc)::[])

	  ) ([], [], []) lind

	in
	let rw = List.combine name terms in

	let terms =
	  
	  List.map (

	    fun hd ->
	      
	      let t = rewrite_mutual_def hd rw in
		print (sprintf "%s\n" (string_of_term t state.implicite));
		t

	  ) terms
	  
	in

	let l = List.combine lnc terms in

	  List.fold_left (
	    
	    fun acc hd ->
	      
	      match acc with
		| None -> None
		| Some def ->
		    
		    let (cons, term) = hd in
		      
		      match check_term path term None state.def state.coercion (oracleslist state.oracles) state.overload state.implicite with
			| None -> None
			| Some (te, ty) ->
			    match te with
			      | Ind (x2, la2, ty2, lc2) -> (
				  
				  let def' = VarMap.add x2 (te, ty, TYPE) VarMap.empty in
				    
				  let (def',_) = 
				    List.fold_left (
				      
				      fun l hd ->
					let (def, n) = l in
					let cname = hd in
					  (
					   (VarMap.add 
					      cname 
					      (Cons (n,Cste x2), (largs_foralls (List.nth lc2 n) la2), DATA) 
					      def
					   ),n+1)
					    
					    
				    ) (def', 0) cons in
				    
				    
				    Some (varmap_union def def')
				      
				)
			      | _ -> None
				  
	  ) (Some VarMap.empty) l

      )

    | MutualRecursive lind -> (

	(* (name * (name * term) list * int list * term * term) list *)


	let (name, terms) =
	  
	  List.fold_left (

	    fun acc hd ->
	      
	      let (x, la, ldec, ty, te) = hd in
	      let (name, terms) = acc in
		
	      let te = Phi (x, la, ty, ldec, te) in 
		
		(name @ x::[], terms @ te :: [])

	  ) ([], []) lind

	in
	let rw = List.combine name terms in

	let terms =
	  
	  List.map (

	    fun hd ->
	      
	      rewrite_mutual_def hd rw		

	  ) terms
	  
	in

	  List.fold_left (
	    
	    fun acc hd ->
	      
	      match acc with
		| None -> None
		| Some def ->
		    
		    match hd with
		      | Phi (x, la, ty, ldec, te) -> (
			  
			  match definition2state (Recursive (x, la, ldec, ty, te)) state path with
			    | None -> print_error (sprintf "Probleme: %s\n\n" (string_of_term hd state.implicite)); None
			    | Some def' ->
				Some (varmap_union def def')
				  
			)
			  
		      | _ -> None
			  

	  ) (Some VarMap.empty) terms
	
      )
	

;;

(******************)
(* Typecheck info *)
(******************)

(* bad name *)
type typeckinfo =
  | Coercion of term
  | CoercionAs of term * term
  | Overload of name * term * int
  | Implicite of name * int
;;

let typecheckinfo2state ti state st path =
  match ti with
    | Coercion (te) -> (
	match check_term path te None state.def state.coercion (oracleslist state.oracles) state.overload state.implicite with
	  | None -> print_error "Coercion Typecheck error\n\n"; None
	  | Some (te, ty) ->
	      Some (add_coercion te ty st state)


      )

    | CoercionAs (te, tey) -> (
	match check_term path te (Some tey) state.def state.coercion (oracleslist state.oracles) state.overload state.implicite with
	  | None -> print_error "Coercion as Typecheck error\n\n"; None
	  | Some (te, ty) -> 
	      Some (add_coercion te ty st state)
      )


    | Overload (name, te, n) -> (

	match check_term path te None state.def state.coercion (oracleslist state.oracles) state.overload state.implicite with
	  | None -> print_error "Overload Typecheck error\n\n"; None
	  | Some (te, ty) ->
	      Some (add_overload name te n state st)
      )

    | Implicite (name, n) -> (

	Some (add_implicite (concat "." (path::name::[])) n state st)

      )
;;

(*********)
(* proof *)
(*********)

type proof =
  | Lemma of name * term
  | Tactic of tactics
  | Qed
  | Defined
  | Drop
;;

(********)
(* Info *)
(********)

type info =
  | Typecheck of term * term option
  | Simpl of term * term option
  | Interp of term * term option
  | Compute of term * term option
  | VMCompute of term * term option
  | ShowDef
  | ShowCoercion
  | ShowGoal
  | ShowImplicite
  | ShowOverload
  | Show of term
  | ShowTactics
;;

(***********)
(* Control *)
(***********)

type control =
  | Quit
  | Undo
  | Require of name
  | Load of name
  | Open of name
  | Variable of name * term
  | Close
;;

(***********)
(* Command *)
(***********)

type command =
  | CmdDefinition of definition
  | CmdTypeckinfo of typeckinfo
  | CmdProof of proof
  | CmdInfo of info
  | CmdControl of control
;;


(*****************************)


let manageDefinition def = 
  match definition2state def state.tpck (List.hd state.path) with
    | None -> print_error "Definition: Error !!\n\n\n"
    | Some def -> (

	print "\n------------- Definition -------------\n";
	let l = (VarSet.inter ((definition2nameset state.tpck.def) +++ (vmdomain state.tpck.overload)) (vmdomain def)) in
	  if (VarSet.is_empty l) then (


	    List.fold_left (
	      
	      fun tl hd ->
		
		print (sprintf "%s Defined\n" hd);
		
	    ) () (VarSet.elements (vmdomain def));

	    let nstate = empty_state () in
	      nstate.def <- mkdefinitionfromdef (List.hd state.path) def;
	      state.defhist <- nstate :: state.defhist;
	      pushst2inst1 state.tpck nstate;
	      state.hist <- HistDef :: state.hist;

	  ) else (

	    print_error "Error !!\n";
	    List.fold_left (
	      
	      fun tl hd ->

		print_error (sprintf "%s is already defined!\n" hd);
		
	    ) () (VarSet.elements l);
	  );

	  print "--------------------------------------\n\n";
      )
;;


let manageTypechekinfo ti =
  let nstate = empty_state () in
    match typecheckinfo2state ti state.tpck nstate (List.hd state.path) with
      | None -> ()
      | Some _ -> 
	  state.defhist <- nstate :: state.defhist;
	  pushst2inst1 state.tpck nstate;
	  state.hist <- HistDef :: state.hist
  
;;

(***********************************)
(* to put somewhere else *)

let rec print_subgoal_context c =
  match c with
    | [] -> ();
    | (hd1, hd2) :: tl ->
        print (sprintf "%s : %s\n" hd1 (string_of_term hd2 state.tpck.implicite));
        print_subgoal_context tl;;


let print_subgoal ctxt ty =
  print "\n\n";
  print (sprintf "\n\n%s----------------------------\n\n%s\n\n"
	   (string_of_listvarterm ctxt state.tpck.implicite)
	   (string_of_term ty state.tpck.implicite));  
;;

let rec print_subgoals sg =
  match sg with
    | [] -> print "\n\n";
    | (hd1, hd2, hd3) :: tl ->
        print (sprintf "----------------------------\n%s\n\n"          
		 (string_of_term hd3 state.tpck.implicite));
        print_subgoals tl
;;

let print_subgoals_ctxt () =
  match (state.prooftree) with
    | [] -> print_error "Error: Not in proof mode\n\n";
    | ((hd1,hd2,hd3)::tl,(ln,te,ty)) :: tl2 ->  (

        print "\n\n";
        (*print_subgoal_context (readable_context_fp hd1 state.def);*)
        print_subgoal_context hd1;
        print_subgoals ((hd1,hd2,hd3)::tl);
        
      );
    | ([], g) :: tl -> print "No more subgoals\n\n";;

class axiom my_name my_type =
object (self)
  inherit [term] pObj
  (*method uuid = 0*)
  method get_name = my_name
  method get_type = my_type
  method equal = (fun o -> (o#get_name = self#get_name) && (term_eq o#get_type self#get_type state.tpck.def))
  method pprint = (fun args implicite -> concat "" (self#get_name :: (string_of_listterm args implicite) :: []))
  method my_self = (self :> term pObj)
  method exec = (fun args def -> App (Obj (self#my_self), simpl_listterm args def))
  method show = (fun implicite -> string_of_term self#get_type implicite)
end;;

let rec remove_all_tactic l =
  match l with
    | [] -> []
    | hd :: tl ->
        match hd with
          | HistTactic s ->
              remove_all_tactic tl
          | _ ->
              l
;;

(***********************************)

(* should put in into some string_ext *)
let rec cutstring name c =  
  try
    let i = String.index_from name 0 c in
      (String.sub name 0 i)::(defname2path (String.sub name (i+1) (String.length name - i - 1)))

  with
    | _ -> name::[]
;;


let rec loadRequired file nstate l retry =

  if (
    List.fold_left (
      
      fun acc hd -> 
	
	(file = hd) || acc
	  
	  
    ) false (l @ (List.flatten state.required))
  ) then (Some l)

  else (

    try
      let file2 = concat "" (file :: ".mo" :: []) in
      let filechannel = open_in file2 in

	(*printf "try loading: %s\n\n" file2;*)
	
      let (l', nstate') = Marshal.from_channel filechannel in

	close_in filechannel;
	
	let i = (VarSet.inter (definitiondomain nstate'.def) ((definitiondomain state.tpck.def) +++ (definitiondomain nstate.def))) in
	  if (not (VarSet.is_empty i)) then (

	    print_error "Already defined terms:\n";
	    List.fold_left (
	      
	      fun tl hd ->
		
		print_error (sprintf "%s is already defined!\n" hd);
		
	    ) () (VarSet.elements i);

	    None

	  ) else (

	    pushst2inst1 nstate nstate';
	    
	    List.fold_left (
	      
	      fun acc hd ->
		
		match acc with
		  | None -> None
		  | Some l ->
		      loadRequired hd nstate l false
			
	    ) (Some (file::l)) l'


	  )  

    with
      | e -> 
	  (
	  match e with
	    | Sys_error _ -> ()
	    | _ -> (*printf "error1\n\n"; flush stdout;*) raise e
	  );

	  try 
	    if retry then (
	      None
	    ) else 
	      let path = getenv "MYMMS_STDLIB_PATH" in
	      let lst = cutstring path ':' in
		List.fold_left (
		  
		  fun tl hd ->
		    
		    match tl with
		      | None ->
			  loadRequired (concat "" (hd :: "/" :: file :: [])) nstate l true
		      | _ -> tl

		) None ("." :: lst)
		
	  with
	    | e -> 
		(
		  match e with
		    | Sys_error _ -> None
		    | _ -> (*printf "error2\n\n"; flush stdout;*) raise e
		);
		
		  
  )

;;

let rec loadExt file pathlist =

  try (
    
    match pathlist with
      | [] -> None
      | hd :: tl ->
	  
	  let filename = (concat "" (hd :: "/" :: file :: ".cmxs" :: [])) in
	    (*printf "try: %s\n" filename;*)
	    loadfile filename;
	    Some ();

  ) with
    | _ -> 
	
	match pathlist with
	  | [] -> None
	  | hd :: tl ->
	      loadExt file tl
;;


let manageControl control =
  match control with
    | Quit -> exit 0
    | Undo -> (
	match state.hist with
	  | [] -> print_error "No command to undo !!\n\n"
	  | HistDef :: tl -> (
	      
	      state.hist <- tl;
	      
	      match (state.defhist) with
		| [] ->
		    print_error "No definitions to undo !!\n\n"

		| hd :: tl ->
		    state.defhist <- tl;
		    popst2inst1 state.tpck hd;


	    )

	  | HistInfo :: tl ->
	      state.hist <- tl;

	  | (HistLemma name) :: tl -> (

	      state.prooftree <- [];
	      state.subgoals <- 0;
	      state.hist <- tl;

	    )

	  | (HistTactic s) :: tl -> (
	      (
		match (state.prooftree) with
		  | [] -> ()
		  | hd :: tl -> 
		      state.prooftree <- tl;
		      print_subgoals_ctxt ();
	      );
	      (match (state.proof) with
		  | [] -> ()
		  | hd :: tl -> 
		      state.proof <- tl;
	      );
	      state.hist <- tl;

	    )

	  | HistRequired :: tl -> (

	      state.hist <- tl;
	      
	      match (state.defhist) with
		| [] ->
		    print_error "No definitions to undo !!\n\n"
		      
		| hd :: tl ->
		    state.defhist <- tl;
		    popst2inst1 state.tpck hd;      


	    )

	  | HistOpen :: tl -> (

	      state.hist <- tl;
	      state.path <- List.tl state.path;

	    )

	  | (HistClose d) :: tl -> (

	      state.hist <- tl;
	      state.path <- d::state.path;

	    )
	  | HistVariable :: tl -> (

	      state.hist <- tl;
	      
	      match (state.defhist) with
		| [] ->
		    print_error "No definitions to undo !!\n\n"

		| hd :: tl ->
		    state.defhist <- tl;
		    popst2inst1 state.tpck hd;
		    state.variable <- List.tl state.variable;

	    )
      )
    | Require file -> (
	
	let nstate = empty_state () in
	  match loadRequired file nstate [] false with
	    | None -> print_error (sprintf "Require: Error (%s)!!\n\n" file);
	    | Some l ->
		
		state.defhist <- nstate :: state.defhist;
		pushst2inst1 state.tpck nstate;
		state.hist <- HistRequired :: state.hist;
		state.required <- l :: state.required;

      )
    | Load file -> (

	clean_state load_state;
	
	if (
	  List.fold_left (
	    
	    fun acc hd -> 
	      
	      (file = hd) || acc
		
		
	  ) false (List.flatten state.required)
	) then (
	  print_error (sprintf "Already Loaded: %s\n" file);
	  List.fold_left (fun acc hd -> print_error (sprintf "%s\n" hd)) () (List.flatten state.required) 
	)
	  
	else (

	  let paths =

	    try (
	      let path = getenv "MYMMS_EXT_PATH" in
	      let lst = cutstring path ':' in
		
		"."::lst
		  
	    ) with 
		
	      | _ -> "." :: []	
		  
		
	  in
	  
	  match loadExt file paths with
	    | None -> print_error (sprintf "Load: Error (%s)!!\n\n" file);
	    | Some _ ->
		
		state.defhist <- load_state :: state.defhist;
		pushst2inst1 state.tpck load_state;
		state.hist <- HistRequired :: state.hist;
		state.required <- (file :: []) :: state.required;
		print (sprintf "Loaded: %s!!\n\n" file);
	      
	)

      )
    | Open d -> (
	
	state.path <- d :: state.path;
	state.hist <- HistOpen :: state.hist;

      )

    | Close -> (
	
	try
	  let d = List.hd state.path in
	    state.path <- List.tl state.path;
	    state.hist <- (HistClose d) :: state.hist;

	with
	  | _ -> ()

      )

    | Variable (v, t) -> (

	(* FIXME: maybe look if the variable is already in *)
	match check_term (List.hd State.state.path) t (Some Type) state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
	  | None -> print_error "Error: Cannot insert variable: bad type !\n\n";
	  | Some (t, _) ->
	      let nstate = empty_state () in
		match insertdef (concat "." ((List.hd state.path):: v ::[])) ((Obj ((new axiom v t) :> term pObj)), t, UNKNOWN) nstate.def with
		  | None ->  print_error "Error: Cannot insert variable: not definable!\n\n";
		  | Some ndef -> 
		      nstate.def <- ndef;                  
		      state.defhist <- nstate :: state.defhist;
		      pushst2inst1 state.tpck nstate;
		      state.hist <- HistVariable :: state.hist;		      
		      state.variable <- v::state.variable;

      )

;;

(*********************************************)

(* Compute *)

let interpretation te ty =
  match check_term (List.hd State.state.path) te ty state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
    | None -> print_error "Interp: Error!!\n\n"; None
    | Some (te, ty) ->
	let te = alpha_term_vars te VarSet.empty in
	(*printf "%s: %s\n\n" (string_of_term te VarMap.empty) (string_of_term ty VarMap.empty);*)
	try (
	  
	  let it = term2iterm te [] state.tpck.def in	  
	  let it = itermexec it [] state.tpck.def in
	  let t = iterm2term it 0 [] [] in
	  (*let t = fold_term t VarSet.empty state.tpck.def in*)
	    
	    (*printf "%s: %s\n\n" (string_of_term t VarMap.empty) (string_of_term ty VarMap.empty);*)
	    
	    match check_term (List.hd State.state.path) t (Some ty) state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload VarMap.empty with
	      | None -> 
		  None
	      | Some (te, ty) -> Some (te, ty)
	) with
	  | Translationterm2iterm s -> print_error (sprintf "%s\n" s); None
	  | Translationiterm2term -> None
	  | Itermexec s -> print_error (sprintf "%s\n" s); None
	  | Failure s -> print_error (sprintf "%s\n" s); None
;;

let vmcompute te ty =
  match check_term (List.hd State.state.path) te ty state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
    | None -> print_error "Interp: Error!!\n\n"; None
    | Some (te, ty) ->
	print (sprintf "VMCompute value of type: %s\n\n" (string_of_term ty State.state.tpck.implicite));
	(*printf "VMCompute value of type: %s\n\n" (string_of_term ty State.state.tpck.implicite);*)
	try (
	  
	  let it = term2iterm te [] state.tpck.def in
	  let (c, m, l) = translate_lambda2cmd1  "main" 0 it (VarMap.empty) state.tpck.def in
	    (*printf "translation lambda -> cmd1\n\n"; flush stdout;*)
(*
	    let s = String.concat "," (
	      List.map (fun hd ->			  
			  let hdref = block1_deflabel (VarMap.find hd m) in
			  let hdref = String.concat "," (VarSet.elements hdref) in
			    String.concat "" (hd :: "(" :: hdref :: ")" :: [])
		       ) 
		(VarSet.elements (vmdomain m))
	    ) in
	      printf "domain = %s\n\n" s;
*)
	    (* the "final" return *)
	  let c = c @ Return1::[] in
	  let b = concat_block1_2 c m in
	    (*printf "concat block\n\n"; flush stdout;*)
	  let m = build_label_offset b 0 in
	    (*printf "build label offset\n\n"; flush stdout;*)
	  let c = Array.of_list (translate_block1_to_block2 b m) in
	    (*printf "|block| = %d\n\n" (Array.length c); flush stdout;*)
	    (*printf "translate block1 -> block2\n\n"; flush stdout;*)
	  let res = vm_exec2 c 0 [] [] state.tpck.def in
	    (*printf "vmexec\n\n"; flush stdout;*)
	    print (string_of_data2 res); print "\n";
	  let it = data22iterm res in
	    (*printf "data22->iterm\n\n"; flush stdout;*)
	  let t = iterm2term it 0 [] [] in
	    (*printf "iterm->term\n\n"; flush stdout;*)
	    
	    match check_term (List.hd State.state.path) t (Some ty) state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
	      | None -> None
	      | Some (te, ty) ->
		  Some (te, ty)
		  (*Some (fold_term te VarSet.empty state.tpck.def, fold_term ty VarSet.empty state.tpck.def)*)
		
	) with
	  | Translationterm2iterm s -> print_error (sprintf "%s\n" s); None
	  | Translationiterm2cmd1 s -> print_error (sprintf "%s\n" s); None
	  | Translationdata22iterm s -> print_error (sprintf "%s\n" s); None
	  | VMExec s -> print_error (sprintf "%s\n" s); None
	  | Failure s -> print_error (sprintf "%s\n" s); None
	  | Not_found -> None
;;


(*********************************************)


let manageInfo info =
  match info with
    | Typecheck (te, ty) -> (

	(
	  match check_term (List.hd State.state.path) te ty state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
	    | None -> print_error "Typecheck: Error!!\n\n"
	    | Some (te, ty) ->
		print (sprintf "%s: %s\n\n" (string_of_term te state.tpck.implicite) (string_of_term ty state.tpck.implicite));
		state.hist <- HistInfo :: state.hist
	)



      )
    | Simpl (te, ty) -> (

	  match simpl_term (List.hd State.state.path) te ty state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
	    | None -> print_error "Simpl: Error!!\n\n"
	    | Some (te, ty) ->
		print (sprintf "%s: %s\n\n" (string_of_term te state.tpck.implicite) (string_of_term ty state.tpck.implicite));
		state.hist <- HistInfo :: state.hist
		  
      )
    | Interp (te, ty) -> (
	
	match interpretation te ty with
	  | None -> print_error "Interp: Error!!\n\n"
	  | Some (te, ty) ->
	      print (sprintf "%s: %s\n\n" (string_of_term te state.tpck.implicite) (string_of_term ty state.tpck.implicite));
	      state.hist <- HistInfo :: state.hist		  

      )
    | VMCompute (te, ty) -> (

	match vmcompute te ty with
	  | None -> print_error "VMCompute: Error!!\n\n"
	  | Some (te, ty) ->
	      print (sprintf "%s: %s\n\n" (string_of_term te state.tpck.implicite) (string_of_term ty state.tpck.implicite));
	      state.hist <- HistInfo :: state.hist


      )
    | Compute (te, ty) -> (

	(
	  #ifdef LLVM

	  match check_term (List.hd State.state.path) te ty state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
	    | None -> print_error "Compute: Error!!\n\n"
	    | Some (te, ty) ->
		(*printf "%s: %s\n\n" (string_of_term te state.tpck.implicite) (string_of_term ty state.tpck.implicite);*)
		try (
		  let m_value = compile te ty in
		  let _ = ExecutionEngine.run_function m_value [||] the_execution_engine in
                    dump_value m_value;		      
		    state.hist <- HistInfo :: state.hist
		) with 
		  | Jitinit.Error s ->
		      print_error (sprintf "Compute Error: %s\n\n" s)
		  | _ -> print_error (sprintf "Compute Error!! \n\n")

	   #endif	

	)	

      )
    | ShowDef -> (

	let l = definition2ext [] state.tpck.def in
	  
	  print "-------------------------\nDefinitions:\n\n";
	  
	  List.fold_left (
	    
            fun tl hd ->
              let (name, (te, ty, nature)) = hd in
		print (sprintf "%s := %s : %s [%s]\n\n"
			 name
			 (string_of_term te state.tpck.implicite)
			 (string_of_term ty state.tpck.implicite)
			 (string_of_nature nature));
		
	  ) () l; 
	  print "-------------------------\n"; flush stdout;

	  state.hist <- HistInfo :: state.hist


      )
    | ShowCoercion -> (

	let l = state.tpck.coercion in
	  
	  print "Coercions:\n";
	  
	  List.fold_left (
	    
            fun tl hd ->
              let (te, ty) = hd in
		print (sprintf " %s: %s  \n"
			 (string_of_term te state.tpck.implicite)
			 (string_of_term ty state.tpck.implicite));
	  ) () l; print "\n";
	state.hist <- HistInfo :: state.hist

      )
    | ShowGoal -> (

	print_subgoals_ctxt();
	state.hist <- HistInfo :: state.hist

      )

    | ShowTactics -> (

	if (List.length state.prooftree = 0) then
	  print_error "Not in proof mode\n"
	else (

	  let ltact = state.proof in
	  let s =
	    String.concat "\n" 
	      (List.map
		 (
		   fun x ->
		     String.concat "" (string_of_tactic x state.tpck.implicite :: "." :: [])
		 ) (rev ltact)
	      ) in
	    print (sprintf "Tactics:\n-------\n%s\n--------\n\n" s)

	);

	state.hist <- HistInfo :: state.hist

      )

    | ShowImplicite -> (

	let l = vmext state.tpck.implicite in
	  
	  print "Definitions:\n";
	  
	  List.fold_left (
	    
            fun tl hd ->
              let (name, n) = hd in
		print (sprintf "%s  [%d]\n"
			 name n);
		
	  ) () l; print "\n";
	  state.hist <- HistInfo :: state.hist

      )

    | ShowOverload -> (

	let l = vmext state.tpck.overload in
	  
	  print "Overloading:\n";
	  
	  List.fold_left (
	    
            fun tl hd ->

	      let (name, overl) = hd in
		
		List.fold_left (
		  
		  fun acc hd -> 
		    
		    let (te, n) = hd in
		      print (sprintf "%s:= %s [%d] \n"
			       name (string_of_term te state.tpck.implicite) n);
		      
		) () overl
		  
	  ) () l; print "\n";
	  state.hist <- HistInfo :: state.hist

      )

    | Show te -> (

	(
	  match check_term (List.hd State.state.path) te None state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
	    | None -> print_error "Show: Error!!\n\n"
	    | Some (te, ty) ->
		print (sprintf "%s: %s\n\n" (show (unfold_term te state.tpck.def) state.tpck.implicite state.tpck.def) (string_of_term ty state.tpck.implicite));
		state.hist <- HistInfo :: state.hist
	)	

      )


;;


let manageProof pr =
  match pr with
    | Lemma (n, t) -> (

	if (not (List.length state.prooftree = 0)) then
	  print_error "Already in proof mode \n\n"
	else (

	  match check_term (List.hd State.state.path) t (Some Type) state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite with
              
            | Some (te, ty) -> (
		
		state.subgoals <- 0;
		let subgoal_name = (concat "" ("subgoal"::(string_of_int state.subgoals):: [])) in 
		  
		  state.prooftree <- ((([],subgoal_name, te)::[], (n, Var subgoal_name, te)) :: []);          
		  state.proof <- [];
		  state.hist <- (HistLemma n) :: state.hist;                            
		  print_subgoals_ctxt()
		    
              )
		
            | _ -> (
		
		print_error "Error: invalide type !\n\n";
		
              )
	    
	)  

      )
    | Qed -> (

	match state.prooftree with
	  | [] -> print_error "Error: Not in proof mode\n\n";
	  | ([], (n, te,ty)) :: tl -> (
              match check_term (List.hd State.state.path) te (Some ty) state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite                    
              with
		| Some (te, ty) -> (

                    print "proof complete.\n\n";
                    state.prooftree <- [];
		    state.proof <- [];
                    state.subgoals <- 0;
		    let nstate = empty_state () in
		      match insertdef (concat "." ((List.hd state.path)::n::[])) ((Obj ((new axiom n ty) :> term pObj)), ty, UNKNOWN) nstate.def with
			| None ->  print_error "Error: Cannot insert def!\n\n";
			| Some ndef -> 
			    nstate.def <- ndef;                  
			    state.hist <- (remove_all_tactic (state.hist));
			    (match state.hist with
			       | [] -> state.hist <- []
			       | hd :: tl -> state.hist <- tl
			    );
			    state.defhist <- nstate :: state.defhist;
			    pushst2inst1 state.tpck nstate;
			    state.hist <- HistDef :: state.hist;		      
			      
		  )
		| _ ->
                    print_error "Error: proof does not type!\n\n";
                    print_term te state.tpck.implicite; print_error "\n\n";
		    
            )
	  | _ -> 
              print_error "proof not complete!\n\n";
              print_subgoals_ctxt()

      )
    | Defined -> (

	match state.prooftree with
	  | [] -> print_error "Error: Not in proof mode\n\n";
	  | ([], (n, te,ty)) :: tl -> (
              match check_term (List.hd State.state.path) te (Some ty) state.tpck.def state.tpck.coercion (oracleslist state.tpck.oracles) state.tpck.overload state.tpck.implicite                    
              with
		| Some (te, ty) -> (

                    print "proof complete.\n\n";
                    state.prooftree <- [];
                    state.proof <- [];
		    state.subgoals <- 0;
		    let nstate = empty_state () in
		      match insertdef (concat "." ((List.hd state.path)::n::[])) (te, ty, UNKNOWN) nstate.def with
			| None ->  print_error "Error: Cannot insert def!\n\n";
			| Some ndef -> 
			    nstate.def <- ndef;                  
			    state.hist <- (remove_all_tactic (state.hist));
			    (match state.hist with
			       | [] -> state.hist <- []
			       | hd :: tl -> state.hist <- tl
			    );
			    state.defhist <- nstate :: state.defhist;
			    pushst2inst1 state.tpck nstate;
			    state.hist <- HistDef :: state.hist;		      
			    
		  )
		| _ ->
                    print_error "Error: proof does not type!\n\n";
                    print_term te state.tpck.implicite; print_error "\n\n";
		    
            )
	  | _ -> 
              print_error "proof not complete!\n\n";
              print_subgoals_ctxt()
	
      )

    | Drop -> (
	
	if (List.length state.prooftree = 0) then
	  print_error "Not in proof mode\n"
	else (
	  state.prooftree <- [];
          state.subgoals <- 0;
	  state.hist <- (remove_all_tactic (state.hist));
	  
	)

      )

    | Tactic s -> (
	
	match state.prooftree with
	  | [] -> print_error "Error: Not in proof mode\n\n";
	  | (lgh, lgg) :: tl -> (
              match (applytactics s 1 lgh lgg  state.tpck.def state.tpck.coercion state.tpck.oracles state.tpck.overload state.tpck.implicite) with
		| None -> print_error "Error: Cannot apply Tactic\n\n";
		| Some (lgh,lgg,n) ->
                print (sprintf "%d subgoals generated\n\n" n);
                    state.prooftree <- (lgh,lgg) :: state.prooftree;
		    state.proof <- s::state.proof; 
                    state.hist <- (HistTactic s) :: state.hist;                                     
		    
            );
              print_subgoals_ctxt();

      )
;;


let manageCommand cmd =
  match cmd with
    | CmdDefinition def ->
	manageDefinition def
    | CmdTypeckinfo ti ->
	manageTypechekinfo ti
    | CmdInfo info ->
	manageInfo info
    | CmdControl control ->
	manageControl control
    | CmdProof pr ->
	manageProof pr	
;;




