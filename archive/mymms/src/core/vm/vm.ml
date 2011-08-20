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

open Def;;
open Varmap;;
open Varset;;
open Interp;;
open Printer;;
open String;;
open List;;
open Printf;;
open Freshness;;
open Listext;;
open Definition;;
open Term;;
open Rewrite;;
open Simpl;;
open Unfold;;
open Output;;

(***************)
(* First stage *)
(***************)

type label = string;;

type data1 =
  | DInd of (var * (var * term) list * term * term list) * data1 list
  | DCons of (int * term * data1 list) 
  | DObj of term pObj * data1 list
  | DType 
;;


exception Translationdata12iterm of string
;;

let rec data12iterm t =
  match t with
    | DObj (o, l) -> 
	let l = List.map (fun x -> data12iterm x) l in
	  IApp (IObj o, l)

    | DType -> IType
    | DCons (n, i, l) ->
	let l = List.map (fun x -> data12iterm x) l in
	  IApp (ICons (n, i), l)
    | DInd ((v, la, ty, lcons), l) ->
	let l = List.map (fun x -> data12iterm x) l in
	  IApp (IInd(v, la, ty, lcons), l)

;;

(* command language (with labelique link) *)
type cmd1 =
  | Closure1 of (label * int)
  | Return1 
  | Switch1 of (label list)
  | Apply1
  | Access1 of int
  | Push1 of data1
  | Data1 of int * term * int
  | Call1 of label
  | Label1 of label * cmd1
  | Jmp1 of label
  | Nop1
;;

type block1 = cmd1 list
;;

let cmd1_deflabel l b =
  match b with
    | [] -> []
    | hd :: tl ->
	(Label1 (l, hd))::tl
;;

(* get the set of labels *)
let rec block1_reflabel b =
  List.fold_left (
    fun acc hd ->
      match hd with
	| Closure1 (l, _) -> l ++ acc
	| Switch1 l -> List.fold_left (fun acc hd -> hd ++ acc) VarSet.empty l
	| Call1 l -> l ++ acc
	| Label1 (l ,b) -> (block1_reflabel (b::[])) +++ acc
	| Jmp1 l -> l ++ acc
	| _ -> acc

  ) VarSet.empty b
;;

(* get the set of labels *)
let rec block1_deflabel b =
  List.fold_left (
    fun acc hd ->
      match hd with	  
	| Label1 (l, b) -> l ++ (acc +++ (block1_deflabel (b::[])))
	| _ -> acc

  ) VarSet.empty b
;;


exception Translationiterm2cmd1 of string

(* returns (cmd1 * cmd1 VarMap.t) *)
let rec translate_lambda2cmd1
    (curlabel: label)
    (curlevel: int)
    (t: iterm)
    (m: block1 VarMap.t) 
    def =
  match t with
    | IVar v ->
	(Access1 v::[], m, curlevel)
    | ILambda t ->
	let (n, t) = (
	  let rec f te = (match te with
			   | ILambda te' -> let (n, te'') = f te' in (n + 1, te'')
			   | _ -> (1, te)
			) in
	    f t	    
	) in
	let m_domain = vmdomain m in
	let new_module = fresh_name_list_name (curlabel ++ m_domain) "@closure" in
	let new_m = VarMap.add new_module [] m in
	let (c, m, l) = translate_lambda2cmd1 new_module 0 t new_m def in
	let new_m = VarMap.remove new_module m in
	let c = cmd1_deflabel new_module (c @ Return1::[]) in
	let m = VarMap.add new_module c new_m in
	let c = Closure1 (new_module, n) in
	  (c::[], m, curlevel)	  

    | ICste (c, _) -> (
	(*printf "%s --> Cste: %s: " curlabel c;*)
	if (vsin c (vmdomain m)) then (
	  (*printf "already there\n";*)
	  (Call1 c::[], m, curlevel)

	) else (
	  match finddef c def with
	    | None -> raise (Translationiterm2cmd1 (String.concat "" ("unknown constante:\n" :: 
									c :: []
								     ))
			    )
	    | Some (_, (te, ctype, _)) -> (
		(*printf "added\n";*)
		let cmd = term2iterm te [] def in
		  match cmd with
		    | ICons (i, te) ->
			((Push1 (DCons (i, te, [])))::[], m, curlevel)

		    | IInd (v, la, ty, lcons) ->
			((Push1 (DInd ((v, la, ty, lcons), [])))::[], m, curlevel)

		    | _ -> (
			let (cmd, m, l) = translate_lambda2cmd1 c 0 cmd m def in
			let cmd = cmd1_deflabel c (cmd @ (Return1::[])) in
			let m = VarMap.add c cmd m in
			  (Call1 c::[], m, curlevel)
		      )
	      )
	)    
      )
		  
    | IObj o ->
	((Push1 (DObj (o, [])))::[], m, curlevel)

    | IApp (f, args) -> (


	let (cargs, margs, largs) =
	  List.fold_left (

	    fun acc hd ->

	      let (c, m , l) = acc in
	      let (c' , m' , l') = translate_lambda2cmd1 curlabel l hd m def in
		(c @ c', m', l')

	  ) ([], m, curlevel) (rev args) in

	let (fc, fm, fl) = translate_lambda2cmd1 curlabel largs f margs def in	  
	  (cargs @ fc @ (list_of_n_elt Apply1 (List.length args)), fm, fl)

      )

    | IType ->
	((Push1 DType)::[], m, curlevel)

    | ICons (i, te) ->
	((Push1 (DCons (i, te, [])))::[], m, curlevel)

    | IInd (v, la, ty, lcons) ->
	((Push1 (DInd ((v, la, ty, lcons), [])))::[], m, curlevel)


    | IPhi (x, la, ty, _, body) -> (

	let entry_label = String.concat "_" (curlabel :: (string_of_int curlevel) :: []) in
	let new_m = VarMap.add entry_label [] m in	  
	let new_term = largs_lambdas (rewrite_term_var_term body x (Cste entry_label)) la in
	let new_term = term2iterm new_term [] def in
	let (c, m, curlevel) = translate_lambda2cmd1 curlabel (curlevel + 1) new_term new_m def in
	let m = VarMap.remove entry_label m in
	  (cmd1_deflabel entry_label c, m, curlevel)

      )

    | IMatch (te, ldes, ind) -> (

	let (cte, m, curlevel) = translate_lambda2cmd1 curlabel curlevel te m def in	  
	let exit_label = String.concat "_" (curlabel :: (string_of_int curlevel) :: []) in
	let (cldes, m, curlevel, labels, _) = List.fold_left (
	  fun acc hd ->
	    let (c, m, curlevel, llbel, n) = acc in
	    let entry_label = String.concat "_" (curlabel :: (string_of_int curlevel) :: []) in
	    let nbapply = (match ind with
			     | Ind (x, la, ty, lcons) ->
				 length la + length (fst (decomp_foralls (List.nth lcons n)))
			     | _ -> raise (
				 Translationiterm2cmd1 
				   (String.concat "" ("VM Cannot translate match destructor:\n" :: 
							("???") :: []
						     )
				   )
			       )
			  ) in
	    let (c', m, curlevel) = translate_lambda2cmd1 curlabel (curlevel + 1) (List.nth ldes n) m def in	  
	    let c' = c' @ (list_of_n_elt Apply1 nbapply) @ (Jmp1 exit_label)::[] in
	    let c' = cmd1_deflabel entry_label c' in
	      (c @ c', m, curlevel, llbel @ entry_label::[], n+1)

	) ([], m, (curlevel + 1), [], 0) ldes in

	  (cte @  (Switch1 labels) :: cldes @ (Label1 (exit_label, Nop1)::[]), m, curlevel)

      )

    | _ ->
	raise (
	  Translationiterm2cmd1 
	    (String.concat "" ("VM Cannot translate:\n" :: 
			 ("???") :: []
		      )
	    )
	)
;;

exception Concat_block_notfound

let rec rec_concat_block1 b m deflabel missinglabel =
    if (VarSet.is_empty missinglabel) then
      b else
	let next_block =
	  VarMap.fold (

	    fun key b acc ->
	      match acc with
		| Some _ -> acc
		| _ -> 
		    let deflabel = block1_deflabel b in
		    let goodlabel = VarSet.inter missinglabel deflabel in
		      if (VarSet.is_empty goodlabel) then
			acc
		      else (
			(*
			printf "add block: %s\n" key;
			printf "deflabel: %s\n" 	    
			  (
			    let hdref = block1_deflabel b in
			    let hdref = String.concat "," (VarSet.elements hdref) in
			      String.concat "" ("(" :: hdref :: ")" :: [])
			  ); 
			printf "reflabel: %s\n\n" 	    
			  (
			    let hdref = block1_reflabel b in
			    let hdref = String.concat "," (VarSet.elements hdref) in
			      String.concat "" ("(" :: hdref :: ")" :: [])
			  ); 
			*)

			let reflabel = block1_reflabel b in
			  Some (key, b, deflabel, reflabel)
		      )
	  ) m None in
	  match next_block with
	    | None -> 
		VarSet.fold (
		  fun v acc ->
		    print_error (sprintf "cannot find: %s\n" v)
		) missinglabel ();
		raise Concat_block_notfound
	    | Some (key, b1, deflabel1, reflabel1) ->
		rec_concat_block1 
		  (b @ b1) 
		  (VarMap.remove key m) 
		  (deflabel1 +++ deflabel)
		  ((VarSet.diff missinglabel (deflabel1 +++ deflabel)) +++ (VarSet.diff reflabel1 (deflabel1 +++ deflabel)))
;;
	  
let concat_block1 b m =
  let reflabel = block1_reflabel b in
  let deflabel = block1_deflabel b in
  let missinglabel = VarSet.diff reflabel deflabel in
    rec_concat_block1 b m deflabel missinglabel
;;

let concat_block1_2 b m =
  List.fold_left (
    fun acc hd ->
      acc @ hd 
  ) b (List.map (fun x -> VarMap.find x m) (VarSet.elements (vmdomain m)))
;;

let rec build_label_offset b offset =
  match b with
    | [] -> VarMap.empty
    | hd :: tl ->
	match hd with
	  | Label1 (l, b) ->
	      (*printf "label: %s\n" l;*)
	      varmap_union (VarMap.add l offset (build_label_offset (b::[]) offset))
		(build_label_offset tl (offset+1))
	  | _ -> build_label_offset tl (offset+1)
;;

(****************)
(* Second stage *)
(****************)

type address = int
;;

type data2 =
  | DClos2 of (address * data2 list * int * data2 list)
  | DCons2 of (int * term * data2 list) 
  | DInd2 of (var * (var * term) list * term * term list) * data2 list
  | DObj2 of term pObj * data2 list
  | DType2 
  | DEnv2 of data2 list
  | DAdr2 of address
;;

let rec data1todata2 d =
  match d with
    | DCons (n, t, l) ->
	DCons2 (n, t, List.map (fun x -> data1todata2 x) l)
    | DInd (te, l) ->
	DInd2 (te, List.map (fun x -> data1todata2 x) l)
    | DObj (o, l) -> DObj2 (o, List.map (fun x -> data1todata2 x) l)
    | DType -> DType2
;;

(* command language (after linking) *)
type cmd2 =
  | Closure2 of (address * int)
  | Return2 
  | Switch2 of (address array)
  | Apply2 
  | Access2 of int
  | Push2 of data2
  | Data2 of  int * term * int
  | Call2 of address
  | Jmp2 of address
  | Nop2
;;

type block2 = cmd2 list;;

(* returns cmd2 *)
let rec translate_cmd1_to_cmd2 
    (c: cmd1) m =
  match c with
    | Closure1 (l, n) -> (
	try
	  Closure2 (VarMap.find l m, n)
	with
	  | _ -> printf "Not found label: %s\n\n" l; flush stdout; raise Not_found;
      )
    | Return1 -> Return2
    | Switch1 l ->
	Switch2 (
	  Array.of_list
	    (
	      List.map (fun l -> 
			  try
			    VarMap.find l m
			  with
			    | _ -> print_error (sprintf "Not found label: %s\n\n" l); raise Not_found;			     
		       ) l
	    )
	)
    | Apply1 -> Apply2
    | Access1 v -> Access2 v
    | Push1 d -> Push2 (data1todata2 d)
    | Data1 (n, ind, nba) -> Data2 (n, ind, nba)
    | Call1 l -> (
	try
	  Call2 (VarMap.find l m)
	with
	  | _ -> print_error (sprintf "Not found label: %s\n\n" l); raise Not_found;
      )
    | Label1 (l, c) -> translate_cmd1_to_cmd2 c m
    | Jmp1 l -> (
	try
	  Jmp2 (VarMap.find l m)
	with
	  | _ -> print_error (sprintf "Not found label: %s\n\n" l); raise Not_found;
      )
    | Nop1 -> Nop2 
	  
;;

let string_of_cmd2 c = 
  match c with
    | Closure2 (l, n) ->
	"Closure"
    | Return2 -> 
	"Return"
    | Switch2 l ->
	"Switch"
    | Apply2 -> 
	"Apply"
    | Access2 v -> 
	"Access"
    | Push2 d -> 
	"Push"
    | Data2 (n, ind, nba) -> 
	"Data"
    | Call2 l -> 
	"Call"
    | Jmp2 l -> 
	"Jmp"
    | Nop2 -> 
	"Nop2"
;;


let translate_block1_to_block2 b m =
  List.map (fun c -> translate_cmd1_to_cmd2 c m) b
;;


let rec string_of_data2 t =
  match t with
    | DObj2 (o, l) -> "DObj2"
    | DType2 -> "DType2"
    | DCons2 (n, i, l) ->
	"DCons2"
    | DInd2 (_, _) -> "DInd2"
    | DAdr2 a -> 
	"DAdr2"
    | DEnv2 e -> 
	"DEnv2"
    | DClos2 (a, l, n, args) ->
	"DClos2"
;;



exception Translationdata22iterm of string
;;

let rec data22iterm t =
  match t with
    | DObj2 (o, l) -> 
	let l = List.map (fun x -> data22iterm x) l in
	  IApp (IObj o, l)

    | DType2 -> IType
    | DCons2 (n, i, l) ->
	let l = List.map (fun x -> data22iterm x) l in
	  IApp (ICons (n, i), l)
    | DAdr2 a -> 
	raise (Translationdata22iterm "data22iterm: Address")
    | DEnv2 e -> 
	raise (Translationdata22iterm "data22iterm: Env")
    | DClos2 (a, l, n, args) ->
	raise (Translationdata22iterm "data22iterm: Closure")
    | DInd2 ((v, la, ty, lcons), l) ->
	let l = List.map (fun x -> data22iterm x) l in
	  IApp (IInd(v, la, ty, lcons), l)

;;

exception Translationiterm2data2 of string
;;

let rec iterm2data2 t def =
  match t with
    | IApp (IObj o, l) ->
	DObj2 (o, List.map (fun x -> iterm2data2 x def) l)
    | IObj o ->
	DObj2 (o, [])
    | IApp (ICons (n, i), l) ->
	DCons2 (n, i, List.map (fun x -> iterm2data2 x def) l)
    | ICons (n, i) ->
	DCons2 (n, i, [])
    | IApp (IInd(v, la, ty, lcons), l) ->
	DInd2 ((v, la, ty, lcons), List.map (fun x -> iterm2data2 x def) l)
    | IInd(v, la, ty, lcons) ->
	DInd2 ((v, la, ty, lcons), [])
    | IType -> DType2
    | ICste (c, _) -> iterm2data2 (term2iterm (unfold_cste c def) [] def) def
    | _ -> raise (Translationiterm2data2 "Connot translate item2data2")
;;

exception VMExec of string

type vmstate = {
  mutable code: cmd2 array;
  mutable pc: int;
  mutable env: data2 list;
  mutable stack: data2 list;
};;



let rec vm_exec2     
    (c: cmd2 array) 
    (pc: int)
    (env: data2 list)
    (stack: data2 list)
    def : data2 = 
  let st = {
    code = c;
    pc = pc;
    env = env;
    stack = stack;
  } in
  let ended = ref true in
  let res = ref DType2 in
  while !ended do
    match st.code.(st.pc) with
      | Closure2 (a, n) -> (
	  st.pc <- st.pc + 1;
	  st.stack <- ((DClos2 (a, st.env, n, [])) :: st.stack);
	)
      |  Return2 -> (
	   match st.stack with
	     | hd :: [] -> (
		 res := hd;
		 ended := false;
	       )
	     | hd :: (DAdr2 ret) :: (DEnv2 env) :: tl -> (
		 st.pc <- ret;
		 st.env <- env;
		 st.stack <- hd :: tl;
	       )
	     | [] -> raise (VMExec ("return with nothing to return"))
	 )
      | Access2 v -> (
	  let v = (
	    try 
	      (List.nth st.env v)
	    with
	      | _ -> raise (VMExec (String.concat " " ("looking for variable" :: (string_of_int v) :: "in an environment of size" :: (string_of_int (List.length st.env)) :: [])))
		  
	  ) in
	    st.pc <- st.pc+1;
	    st.stack <- v::st.stack;
	)
      | Push2 d -> (
	  st.stack <- d::st.stack;
	  st.pc <- st.pc+1;
	)
      | Apply2 -> (
	  
	  match st.stack with
	    | (DClos2 (pc', env', n, args)) :: hd :: tl -> (

		if (List.length args + 1) = n then (
		  st.stack <- (DAdr2 (st.pc + 1)) :: (DEnv2 st.env) :: tl;
		  st.pc <- pc';
		  st.env <- hd :: args @ env';
		) else (
		  st.stack <- (DClos2 (pc', env', n, hd::args)) :: tl;
		  st.pc <- st.pc + 1;
		) 

	      )


	    | (DCons2 (i, te, l) :: hd ::tl) -> (

		st.pc <- st.pc+1;
		st.stack <- ((DCons2 (i, te, l @ hd::[])) :: tl);

	      )

	    | (DInd2 (te, l) :: hd ::tl) -> (

		st.pc <- st.pc+1;
		st.stack <- (DInd2 (te, l @ hd::[])) :: tl;

	      )

	    | (DObj2 (te, l) :: hd ::tl) -> (
		
		try (
		  let t = data22iterm (DObj2 (te, l @ hd::[])) in		    
		  let t = iterm2term t 0 [] [] in
		  let t' = simpl t def in		    
		  let t' = term2iterm t' [] def in 
		  let t'' = iterm2data2 t' def in	
		    st.pc <- st.pc+1;
		    st.stack <- t'' :: tl;
			  
		) with
		  | _ -> 
		      
		      printf "Obj: %s\n" te#get_name;
		      print_error "Cannot translate into data2\n\n" ;
		      st.pc <- st.pc+1;
		      st.stack <- DObj2 (te, l @ hd ::[]) :: tl;

	      )
  
	    | _ -> raise (VMExec (String.concat "" ("No imediaite arg and closure for apply: " :: (List.map (fun x -> string_of_data2 x) st.stack))))

	)
      | Call2 l -> (

	  st.stack <- (DAdr2 (st.pc + 1)) :: (DEnv2 st.env) :: st.stack;
	  st.pc <- l;

	)

      | Switch2 l -> (

	  match st.stack with
	    | (DCons2 (i, te, la)) :: tl ->

		let npc = l.(i) in
		  st.pc <- npc;
		  st.stack <- la @ tl;

	    | hd::tl -> raise (VMExec (String.concat "" ("switch cannot be executed: " :: (string_of_data2 hd) :: [])))

	    | [] -> raise (VMExec (String.concat "" ("switch cannot be executed: " :: "[]" :: [])))

	)

      | Jmp2 l -> (

	  st.pc <- l;

	)

      | Nop2 -> (

	  st.pc <- st.pc+1;

	)
      | _ -> raise (VMExec "Do not know this command")	  
	   
  done;
    !res
;;
