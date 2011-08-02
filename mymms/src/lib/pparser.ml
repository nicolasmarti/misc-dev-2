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

open Stream;;
open Printf;;
open Str;;
open Pprinter;;
open Varmap;;
open Varset;;
open Listext;;
open Pprinter;;


type parserbuffer = {
  mutable inputstream: string Stream.t; 
  mutable bufferstr: Buffer.t;
  mutable beginpointer: int;    
};;

let build_parserbuffer stream = {
  inputstream = stream;
  bufferstr = Buffer.create 0;
  beginpointer = 0;
};;

(* test if we reach the end of the buffer *)
let endofbuffer (pb:parserbuffer) = 
  (pb.beginpointer = Buffer.length pb.bufferstr)

exception NoMatch;;

(* match a regular expression on a buffer:

   takes: * r: a regular expression of Str module
          * pb: a parserbuffer (defined above)
   
   returns: * if the regular expression is matched at the current position of the parserbuffer, the string corresponding
            * otherwise, when the regular expression cannot be matched, raise NoMatch

 *)
let rec match_regexp (r: regexp) (pb:parserbuffer) : string =

  (* if our begin pointer is at the end of the buffer, we should grab another line *)
  if endofbuffer pb then (
    try 
      let str = Stream.next pb.inputstream in
	Buffer.add_string pb.bufferstr str;
	Buffer.add_string pb.bufferstr "\n"	  
    with
      | Stream.Failure -> 
	  raise NoMatch;
	  
  ) else ();    
  (* first look if we can find the expression on the buffer *)
  if string_match r (Buffer.contents pb.bufferstr) pb.beginpointer then
    (* we found it, we grab the string and return it after moving the begin pointer forward*)
    let str = matched_string (Buffer.contents pb.bufferstr) in
    let newpos = pb.beginpointer + String.length str in
      if newpos = Buffer.length pb.bufferstr then (

	try 
	  let str = Stream.next pb.inputstream in
	    Buffer.add_string pb.bufferstr str;
	    Buffer.add_string pb.bufferstr "\n";
	    match_regexp r pb

	with
	  | Stream.Failure -> 
	      pb.beginpointer <- pb.beginpointer + String.length str;
	      str

      ) else (

	      pb.beginpointer <- pb.beginpointer + String.length str;
	      str
      )

  else (
    (* else, maybe we just have the beginning, and need one more line *)
    if string_partial_match r (Buffer.contents pb.bufferstr) pb.beginpointer then (
      (try 
	 let str = Stream.next pb.inputstream in
	   Buffer.add_string pb.bufferstr str;
	   Buffer.add_string pb.bufferstr "\n"
       with
	 | Stream.Failure -> raise NoMatch
      ); match_regexp r pb
    ) else (
      raise NoMatch
    )

  )
;;

(* 
   definition of lexing rule and how to apply it
   + a little example for int
*)

type 'a lexingrule = regexp * (string -> 'a)
;;

let rec applylexingrule (r: 'a lexingrule) (pb:parserbuffer) =
  let str = match_regexp (fst r) pb in
    (snd r) str
;;

let parseintrule = (regexp "[0-9]+", fun (s:string) -> int_of_string s)
;;

(* parsing rules *)

type 'a parsingrule = parserbuffer -> 'a
;;

(* try to apply a parsing rule, if it fails it restore the original beginpointer *)

let tryrule (r: 'a parsingrule) (pb:parserbuffer) =
  let savebegin = pb.beginpointer in
    try 
      r pb
    with
      | NoMatch -> 
	  pb.beginpointer <- savebegin;
	  raise NoMatch
;;

(* disjunction of two parsingrules *)
let orrule (r1: 'a parsingrule) (r2: 'a parsingrule) (pb: parserbuffer) =
  try 
      r1 pb
  with
    | NoMatch -> 
	r2 pb
;;

let (<|>) r1 r2 pb = orrule r1 r2 pb;;

(* a parser for spaces *)
let space = 
  fun pb ->
    try    
      (* it seems a miss something ... but what ?? *)
      applylexingrule ((regexp "[' ' '\t' '\r' '\n']*", fun (s:string) -> ())) pb
    with
      | NoMatch -> ()      
;;

(* add a parsing of following space to some parser *)
let addspace (r: 'a parsingrule) (pb: parserbuffer) =
    let res = r pb in
      space pb;
      res
;;

(* a special case keyword *)
let keyword (s: string) (v: 'a) (pb: parserbuffer) =
  space pb;
  (*let beginp = pb.beginpointer in*)
    try (
      let res = (applylexingrule (regexp_string s, fun _ -> v)) pb in
	space pb;
	res
    )
    with
      | NoMatch ->
	  (*printf "looking for: %s, but next is: '%s'\n" s (String.sub pb.bufferstr beginp (String.length pb.bufferstr - beginp));*)
	  raise NoMatch
;;

(* building a parser from a regexp *)
let regexpparser (s: string) (pb: parserbuffer) : string =
  space pb;
  applylexingrule (regexp s, fun s -> s) pb
;;

(* many combinator *)
let rec many (r: 'a parsingrule) (pb: parserbuffer) : 'a list =
  let hd = (
    try 
      Some (r pb)
    with
      | NoMatch -> None
  ) in
    match hd with
      | None -> []
      | Some hd -> 
	  let tl = many r pb in
	    hd::tl
;;

let many1 (r: 'a parsingrule) (pb: parserbuffer) : 'a list =
  let hd = r pb in
  let tl = many r pb in
    hd::tl
;;

let many2 (r: 'a parsingrule) (pb: parserbuffer) : 'a list =
  let savebegin = pb.beginpointer in
    try 
      let hd1 = r pb in
      let hd2 = r pb in
      let tl = many r pb in
	hd1::hd2::tl
    with
      | NoMatch ->
	  (
	    pb.beginpointer <- savebegin;
	    raise NoMatch
	  )
;;

      
(* not combinator *)
let notp (r: 'a parsingrule) (pb: parserbuffer) : 'a =
  let savebegin = pb.beginpointer in
  let res = (try 
	       let _ = (tryrule r) pb in
		 false
	     with
	       | NoMatch -> true
	    ) in
    if res then ()
    else (
      pb.beginpointer <- savebegin;
      raise NoMatch
    )
;;

(* always returns NoMatch *)
let nokp (pb: parserbuffer) =
  raise NoMatch
;;

(* always returns () *)
let okp (pb: parserbuffer) =
  ()
;;

(* parser asserting that next there is not a string inside the list *)
let notpl (l: string list) : unit parsingrule =
  notp (List.fold_left (
	  fun acc hd ->
	    let parse = keyword hd () in
	      orrule acc parse 
	) nokp l)
;;

(* fold on parser, they are all tried, and it fails if none hold *)
let foldp (l: ('a parsingrule) list) : 'a parsingrule=
  (List.fold_left (
     fun acc hd ->
	 orrule acc (tryrule hd) 
   ) nokp l)
;;

(*************************************************************************)
(*  notation: deep embedding that allow both parsing and pretty printing *)
(*************************************************************************)

(* token: element of the syntax of a rule *)

type token =
  | StringToken of string
  | ReservedToken of string
  | RuleToken of (string * string)
  | NewLineToken 
  | SpaceToken of int
  | BoxToken of token list
;;

type syntax = token list
;;

type 'a parser =
  | Deep of (syntax * 'a)
  | Shallow of (('a pparser -> 'a parsingrule) * ('a pparser -> 'a -> (Pprinter.token list) option))
and 'a rule = {
  priority: int;
  ppretty: bool;
  mutable tried: int list;
  ruleparser: 'a parser;
}
and 'a notation = {
  mutable rule: ('a rule) list;
  mutable errors: int list;
  mutable success: (int * int * 'a) list;
}
and 'a pparser = {
  mutable rules : ('a notation) VarMap.t;
  notations : VarSet.t;
  rewrite: 'a -> ('a VarMap.t) -> 'a;
  unification: 'a -> 'a -> ('a VarMap.t) option;
  reserved: string list;
}
;;

let parser_debug = false;;

let rec pparser_parser (p: 'a pparser) (pb: parserbuffer) : 'a =
  (
    (* we grab the list of top rules *)
    let l = VarSet.elements p.notations in
      foldp (
	List.map (fun hd ->
		    named_parser hd p
		 ) l
      ) pb
  )
and named_parser (s: string) (p: 'a pparser) (pb: parserbuffer) : 'a =
  if parser_debug then (printf "named_parser tested: %s at pos %d\n" s pb.beginpointer; flush stdout) else ();
  try 
    let notation = VarMap.find s p.rules in
    let red = notation_parser notation p pb in
      if parser_debug then (printf "named_parser %s returned with result\n" s; flush stdout) else ();
      red
  with
    | Not_found -> 
	if parser_debug then (printf "named_parser not found: %s\n" s; flush stdout) else ();
	raise NoMatch		
    | NoMatch -> 
	if parser_debug then (printf "named_parser does not match: %s\n" s; flush stdout) else ();
	raise NoMatch
and notation_parser (n: 'a notation) (p: 'a pparser) (pb: parserbuffer) : 'a =
  (* first we look if we already did parse at the curent position *)
  let curpos = pb.beginpointer in
    (* did we failed before ?*)
  let error = List.fold_left (fun acc hd -> 
				if acc then acc else 
				  hd = curpos
			     ) false n.errors in
    if error then raise NoMatch else (
      
      (* we didn't fail, so did we succeed ? *)
      let success = List.fold_left (fun acc hd ->
				      match acc with
					| Some _ -> acc
					| None ->
					    let (s, e, v) = hd in
					      if s = curpos then
						Some (e, v)
					      else
						None
				   ) None n.success in	
	match success with
	  | Some (e, v) ->
	      pb.beginpointer <- e;
	      v
	  | None ->
	      (* nop, so we have to parse it, and we need to remember if we fail or success *)
	      try (
		foldp (List.map (fun hd -> 
				   fun pb ->
				     (* did we already tried this rule *)
				     let tried = hd.tried in
				     let already_tried = List.fold_left (fun acc hd -> 
									   acc || (hd = pb.beginpointer)
									) false tried in
				       if already_tried then (
					 raise NoMatch
				       )
				       else (
					 
					 hd.tried <- pb.beginpointer :: hd.tried;
					 match hd.ruleparser with 
					   | Deep d -> (
					       try (
						 let res = rule_parser d n p pb in
						   hd.tried <- List.tl hd.tried;
						   res
					       )
					       with
						 | NoMatch ->
						     hd.tried <- List.tl hd.tried;
						     raise NoMatch
					     )
					   | Shallow d ->
					       try (
						 let res = (fst d) p pb in
						   hd.tried <- List.tl hd.tried;
						   res
					       )
					       with
						 | NoMatch ->
						     hd.tried <- List.tl hd.tried;
						     raise NoMatch
				       )
				) 
			 (let cmp e1 e2 = e2.priority - e1.priority in
			    List.sort cmp n.rule
			    )
		      ) pb		
	       )
	      with
		| NoMatch -> 
		    n.errors <- curpos::n.errors;
		    raise NoMatch
    )
and rule_parser (rule: (syntax * 'a)) (n: 'a notation) (p: 'a pparser) (pb: parserbuffer) : 'a =
  let beginpos = pb.beginpointer in
  let syntax_parsing_result = syntax_parser (fst rule) n p pb in
  let result = p.rewrite (snd rule) syntax_parsing_result in
  let endpos = pb.beginpointer in
    n.success <- (beginpos, endpos, result)::n.success;
    result    

  
and syntax_parser (s: syntax) (n: 'a notation) (p: 'a pparser) (pb: parserbuffer) : 'a VarMap.t =
  List.fold_left (fun acc hd ->
		    varmap_union acc (token_parser hd n p pb)
		 ) VarMap.empty s
and token_parser (t: token) (n: 'a notation) (p: 'a pparser) (pb: parserbuffer) : 'a VarMap.t =
  match t with
    | StringToken s ->
	notpl p.reserved pb;
	keyword s () pb;
	VarMap.empty;
    | ReservedToken s ->
	keyword s () pb;
	VarMap.empty;
    | NewLineToken ->
	VarMap.empty;
    | SpaceToken _ ->
	VarMap.empty;
    | BoxToken ts ->
	(* should match syntax_parser *)
	syntax_parser ts n p pb
    | RuleToken (r, v) ->
	let res = named_parser r p pb in
	  VarMap.add v res VarMap.empty
;;

let rec position_to_coo (s: string) (pos: int) (curpos: int) (coo: int * int) =
    if (pos = curpos) then 
      coo
    else
      match String.get s curpos with
	| '\n' -> position_to_coo s pos (curpos + 1) (fst coo + 1, 0)
	| _ -> position_to_coo s pos (curpos + 1) (fst coo, snd coo + 1)

;;




let pparser_error (p: 'a pparser) (pb: parserbuffer) = 
  let l = vmext p.rules in
  let list_max_errors = (
    List.concat (
      List.map (
	fun hd ->
	  List.map (
	    fun hd2 ->
	      (fst hd, hd2)
	  ) (snd hd).errors
      ) l
    )
  ) in
  let cmp e1 e2 =
    (snd e2) - (snd e1) in
  let l' = List.sort cmp list_max_errors in
    if List.length l' < 1 then
      printf "No errors\n"
    else
      let coo = position_to_coo (Buffer.contents pb.bufferstr) (snd (List.hd l')) 0 (0,0) in
	printf "constructor %s at position (%d, %d)\n" (fst (List.hd l')) (fst coo) (snd coo)
;;
    



let rec pparser_pprinter (p: 'a pparser) (a: 'a) : Pprinter.token option =
  (
    (* we grab the list of top rules *)
    let l = VarSet.elements p.notations in
      List.fold_left (
	fun acc hd -> 
	  match acc with
	    | Some res -> Some res
	    | _ -> named_pprinter hd p a 
      ) None l      
  )
and named_pprinter (s: string) (p: 'a pparser) (a: 'a) :  Pprinter.token option =
  if parser_debug then (printf "named_pprinter tested: %s\n" s; flush stdout) else ();
  try 
    let notation = VarMap.find s p.rules in
    let red = notation_pprinter notation p a in
      if parser_debug then (
	match red with
	  | Some _ -> printf "named_pprinter %s returned with result\n" s; flush stdout
	  | None -> printf "named_pprinter %s returned with None\n" s; flush stdout
      ) else ();
      red
  with
    | Not_found -> 
	if parser_debug then (printf "named_pprinter not found: %s\n" s; flush stdout) else ();
	None
and notation_pprinter (n: 'a notation) (p: 'a pparser) (a: 'a) : Pprinter.token option =
  if parser_debug then (printf "notation_pprinter tested\n"; flush stdout) else ();
  List.fold_left (
    fun acc hd ->
      match acc with
	| Some res -> Some res
	| None ->
	    if parser_debug then (printf "notation_pprinter rule: %d\n" hd.priority; flush stdout) else ();
	    if hd.ppretty then (
	      match hd.ruleparser with 
		| Deep d -> (
		    match (rule_pprinter d n p a) with
		      | None -> None
		      | Some l -> Some (Pprinter.Box l)		      
		  )
		| Shallow d -> 
		    match (snd d) p a with
		      | None -> None
		      | Some l -> Some (Pprinter.Box l)
	    ) else None	      
  ) None 
    (let cmp e1 e2 = e2.priority - e1.priority in
       List.sort cmp n.rule
    )
and rule_pprinter (rule: (syntax * 'a)) (n: 'a notation) (p: 'a pparser) (a: 'a) : (Pprinter.token list) option =
  if parser_debug then (printf "rule_pprinter tested\n"; flush stdout) else ();
  match p.unification (snd rule) a with
    | None -> None
    | Some s -> tokenlist_pprinter (fst rule) s n p
and tokenlist_pprinter (ts: token list) (s: 'a VarMap.t) (n: 'a notation) (p: 'a pparser) : (Pprinter.token list) option =
  if parser_debug then (printf "tokenlist_pprinter tested\n"; flush stdout) else ();
	List.fold_left (
	  fun acc hd ->
	    match acc with
	      | None -> None
	      | Some l ->
		  match hd with
		    | StringToken s ->
			Some (l @ (Verbatim s)::[])
		    | ReservedToken s ->
			Some (l @ (Verbatim s)::[])
		    | NewLineToken ->
			Some (l @ Newline::[])
		    | BoxToken ts -> (
			match tokenlist_pprinter ts s n p with
			  | None -> None
			  | Some l2 -> Some (l @ (Box l2)::[])
		      )
		    | RuleToken (r, v) -> (
			try ( 
			  let a = VarMap.find v s in
			    match named_pprinter r p a with
			      | None -> None
			      | Some t ->
				  Some (l @ t::[])
			) with
			  | Not_found -> 
			      None
		      )
		    | SpaceToken n -> (			
			Some (l @ (Pprinter.Space n )::[])			
		      )
	) (Some []) ts
	
;;
