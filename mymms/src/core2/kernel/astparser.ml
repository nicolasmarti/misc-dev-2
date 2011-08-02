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

open Str;;
open Pparser;;
open Pprinter;;
open Listext;;
open Varmap;;
open Varset;;
open Printf;;
open Ast;;

(*************************)
(* test of pretty parser *)
(*************************)

let reserved = "let" :: "in" :: "Type" :: "V" :: "match" :: "with" :: "returns" :: "Inductive" :: "Recursive" :: "Definition" :: []
;;

(* the rewriting function *)

let rec astrewrite t subs =
  match t with
    | Type -> Type
    | Symb (n, s) -> (
	try 
	  let t' = VarMap.find s subs in
	    t'
	with
	  | Not_found -> Symb (n, s)
      )
    | App l -> 
	App (List.map (fun hd -> astrewrite hd subs) l)
    | Let (v, t1, t2) -> 
	Let ((try 
		let t' = VarMap.find v subs in
		  match t' with
		    | Symb (n, s) -> s
		    | _ -> v
	      with
		| Not_found -> v
	     ), astrewrite t1 subs, astrewrite t2 subs)
    | Lambda (n, v, t1, t2) -> 
	Lambda (n, (try 
		   let t' = VarMap.find v subs in
		     match t' with
		       | Symb (n, s) -> s
		       | _ -> v
		 with
		   | Not_found -> v)
	       , astrewrite t1 subs, astrewrite t2 subs)
    | Forall (n, v, t1, t2) -> 
	Forall (n, (try 
		   let t' = VarMap.find v subs in
		     match t' with
		       | Symb (n, s) -> s
		       | _ -> v
		 with
		   | Not_found -> v)
		  , astrewrite t1 subs, astrewrite t2 subs)
    | Avar -> Avar
    | Match (t1, t2, t3) -> 
	Match (astrewrite t1 subs, 
	       List.map (fun hd -> 
			   (fst hd, astrewrite (snd hd) subs) 
			) t2, 
	       match t3 with
		 | None -> None
		 | Some t3 -> Some (astrewrite t3 subs)
	      )
    | Phi (x, largs, ty, term, body) -> raise (Failure "astrewrite: case not supported (Phi)")
    | Ind (x, largs, ty, lcons) -> raise (Failure "astrewrite: case not supported (Ind)")
    | Constr (n, ity) -> raise (Failure "astrewrite: case not supported (Cons)")

;;

(* the unification function 

   t1 -> t2

*)

let rec astunification (t1: ast) (t2: ast): (ast VarMap.t) option = 
  match (t1, t2) with
    | (Type, Type) -> Some VarMap.empty
    | (Symb (true, x), t2) -> Some (VarMap.add x t2 VarMap.empty)
    | (Symb (false, x), Symb (false, y)) -> 
	if (x = y) then Some VarMap.empty
	else None
    | (Let (x1, t11, t12), Let (x2, t21, t22)) -> (
	match (astunification t11 t21, astunification t12 t22) with
	  | (Some s1, Some s2) ->
	      Some (varmap_union (varmap_union s1 s2) (VarMap.add x1 (Symb (true, x2)) VarMap.empty))
	  | _ -> None
      )
    | (Lambda (n1, x1, t11, t12), Lambda (n2, x2, t21, t22)) -> (
	if (n1 = n2) then
	  match (astunification t11 t21, astunification t12 t22) with
	    | (Some s1, Some s2) ->
		Some (varmap_union (varmap_union s1 s2) (VarMap.add x1 (Symb (true, x2)) VarMap.empty))
	    | _ -> None
	else
	  None
      )
    | (Forall (n1, x1, t11, t12), Forall (n2, x2, t21, t22)) -> (
	if (n1 = n2) then
	  match (astunification t11 t21, astunification t12 t22) with
	    | (Some s1, Some s2) ->
		Some (varmap_union (varmap_union s1 s2) (VarMap.add x1 (Symb (true, x2)) VarMap.empty))
	    | _ -> None
	else
	  None

      )
    | (App l1, App l2) -> (
	try
	  let us = List.map (fun (hd1, hd2) -> astunification hd1 hd2) (List.combine l1 l2) in
	    List.fold_left (fun acc hd ->
			      match (acc, hd) with
				| (Some acc, Some hd) ->
				    Some (varmap_union acc hd)
				| _ -> None
			   ) (Some VarMap.empty) us
	with
	  | _ -> None
      )
    | (Avar, Avar) -> Some VarMap.empty
    | _ -> None
;;

(* variables *)

let var_notation_rules =
  { priority = 0;
    ppretty = true;
    tried = [];
    ruleparser = (
      (Shallow (
	 (fun p pb ->
	    notpl reserved pb;
	    let v = regexpparser "[A-Za-z0-9]+[A-Za-z0-9_]*" pb in
	      Symb (true, v)
	 ),(
	   fun p a ->
	     match a with
	       | Symb (true, s) -> Some ((Verbatim (String.concat "" (s :: []))) :: [])
	       | _ -> 
		   None
	 )
       )
      )
    )
  }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (
	 (Shallow (
	    (fun p pb ->
	       notpl reserved pb;
	       let v = regexpparser "@[A-Za-z0-9]+[A-Za-z0-9_]*" pb in
		 Symb (false, String.sub v 1 (String.length v - 1))
	    ),(
	      fun p a ->
		match a with
		  | Symb (false, s) -> Some ((Verbatim (String.concat "" ("@" :: s :: []))) :: [])
		  | _ -> 
		   None
	    )
	  )
	 )
       )
  }
  ::  []
;;

let var_notation = {
  rule = var_notation_rules;
  errors = [];
  success = [];
}
;;


(* ast unit *)

let astunit_notation_rules =
  { priority = 0;
    ppretty = true;
    tried = [];
    ruleparser = (Deep (RuleToken ("var", "x") :: [], Symb (true, "x"))) 
  }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (ReservedToken "Type" :: [], Type)) ;
     }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "_"
	    :: [], Avar))
     }
  :: { priority = 1;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (ReservedToken "let" 
			   :: SpaceToken 1
			   :: RuleToken ("var", "x") 
			   :: SpaceToken 1
			   :: StringToken "=" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y") 
			   :: SpaceToken 1
			   :: ReservedToken "in" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "z") 
			   :: [], Let ("x", Symb (true, "y"), Symb (true, "z")))) 
     }
  :: { priority = 1;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "\\" 
			   :: SpaceToken 1
			   :: RuleToken ("lambdaast", "x") 
			   :: [], Symb (true, "x"))) 
     }
  :: { priority = 1;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (ReservedToken "V" 
			   :: SpaceToken 1
			   :: RuleToken ("forallast", "x") 
			   :: [], Symb (true, "x"))) 
     }
  :: { priority = 1;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (RuleToken ("matchast", "x") 
			   :: [], Symb (true, "x"))) 
     }
  :: { priority = 2;
       ppretty = false;
       tried = [];
       ruleparser = (Deep (StringToken "("
			   :: RuleToken ("ast", "x") 
			   :: StringToken ")"
			   :: [], Symb (true, "x")))
     }
  :: []
;;

let astunit_notation = {
  rule = astunit_notation_rules;
  errors = [];
  success = [];
}
;;

(* many1 of ast unit *)

let ast_notation_rules =
  { priority = 0;
    ppretty = true;
    tried = [];
    ruleparser = (Deep (RuleToken ("astunit", "x") 
			:: [], Symb (true, "x")))
  }
  :: { priority = 1;
       ppretty = true;
       tried = [];
       ruleparser = (
	 (Shallow (
	    (fun p pb ->
	       let res = many2 (named_parser "ast" p) pb in
		 App res
	    ), (
	      fun p a ->
		match a with
		  | App l -> (
		      let l' = (List.map (fun hd -> 
					    match (pparser_pprinter p hd) with
					      | None -> (
						  printf "None on:";
						  pprint2ast hd;
						  None
						)
						  
					      | Some l' ->
						  match hd with
						    | App l2 ->
							if List.length l2 > 1 then 
							  Some ((Verbatim "(") :: l' :: (Verbatim ")") :: [])
							else 
							  Some (l' :: [])
						    | _ -> Some (l' :: [])
					 )				    
				  l
			       ) in
			match List.fold_left (fun acc hd ->
						match (acc, hd) with 
						  | (None, _) -> None
						  | (_, None) -> None
						  | (Some acc, Some hd) ->
						      Some (acc @ hd::[])						    						      
					     ) (Some []) l' with
			  | None -> (
			      printf "None on(1):";
			      pprint2ast a;
			      None
			    )
			  | Some l -> Some (concatenate (Space 1) l)			  
		    )
		  | _ -> 
		      match (named_pprinter "astunit" p a) with
			| None -> None
			| Some s -> Some (s::[])
	    )
	  )
	 )
       )
     }
  :: { priority = 4;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (RuleToken ("ast", "x")
			   :: SpaceToken 1
			   :: StringToken "->"
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y")
			   :: [], Forall (Explicite, "@_@", Symb (true, "x"), Symb (true, "y"))))
     }
  :: { priority = 4;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "{"
			   :: RuleToken ("ast", "x")
			   :: StringToken "}"
			   :: SpaceToken 1
			   :: StringToken "->"
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y")
			   :: [], Forall (Hidden, "@_@", Symb (true, "x"), Symb (true, "y"))))
     }
  :: { priority = 4;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "["
			   ::  RuleToken ("ast", "x")
			   :: StringToken "]"
			   :: SpaceToken 1
			   :: StringToken "->"
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y")
			   :: [], Forall (Implicite, "@_@", Symb (true, "x"), Symb (true, "y"))))
     }
  :: { priority = 2;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (RuleToken ("extention", "x") 
			   :: [], Symb (true, "x")))
  }
  ::  []
;;

let ast_notation = {
  rule = ast_notation_rules;
  errors = [];
  success = [];
}
;;

(* lambda notations *)

let lambdaast_notation_rules =
  { priority = 0;
    ppretty = true;
    tried = [];
    ruleparser = (Deep (StringToken "("
			:: RuleToken ("var", "x") 
			:: StringToken ":" 
			:: SpaceToken 1
			:: RuleToken ("ast", "y") 
			:: StringToken ")" 
			:: SpaceToken 1
			:: StringToken "->" 
			:: SpaceToken 1
			:: RuleToken ("ast", "z") 
			:: [], Lambda (Explicite, "x", Symb (true, "y"), Symb (true, "z"))))
  }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "("
			   :: RuleToken ("var", "x") 
			   :: StringToken ":" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y") 
			   :: StringToken ")" 
			   :: SpaceToken 1
			   :: RuleToken ("lambdaast", "z") 
			   :: [], Lambda (Explicite, "x", Symb (true, "y"), Symb (true, "z"))))
     }
  :: { priority = 1;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (RuleToken ("var", "x") 	    
			   :: SpaceToken 1
			   :: RuleToken ("lambdaast", "z") 
			   :: [], Lambda (Explicite, "x", Avar, Symb (true, "z"))))
     }
  :: { priority = 1;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (RuleToken ("var", "x") 	    
			   :: SpaceToken 1
			   :: StringToken "->" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "z") 
			   :: [], Lambda (Explicite, "x", Avar, Symb (true, "z"))))
     }

  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "["
			   :: RuleToken ("var", "x") 
			   :: StringToken ":" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y") 
			   :: StringToken "]" 
			   :: SpaceToken 1
			   :: StringToken "->" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "z") 
			   :: [], Lambda (Implicite, "x", Symb (true, "y"), Symb (true, "z"))))
  }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "["
			   :: RuleToken ("var", "x") 
			   :: StringToken ":" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y") 
			   :: StringToken "]" 
			   :: SpaceToken 1
			   :: RuleToken ("lambdaast", "z") 
			   :: [], Lambda (Implicite, "x", Symb (true, "y"), Symb (true, "z"))))
     }
  :: { priority = 1;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "["
			   :: RuleToken ("var", "x") 	    
			   :: StringToken "]"
			   :: SpaceToken 1
			   :: RuleToken ("lambdaast", "z") 
			   :: [], Lambda (Implicite, "x", Avar, Symb (true, "z"))))
     }
  :: { priority = 1;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "["
			   :: RuleToken ("var", "x") 	    
			   :: StringToken "]"
			   :: SpaceToken 1
			   :: StringToken "->" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "z") 
			   :: [], Lambda (Implicite , "x", Avar, Symb (true, "z"))))
     }

  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "{"
			   :: RuleToken ("var", "x") 
			   :: StringToken ":" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y") 
			   :: StringToken "}" 
			   :: SpaceToken 1
			   :: StringToken "->" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "z") 
			   :: [], Lambda (Hidden, "x", Symb (true, "y"), Symb (true, "z"))))
  }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "{"
			   :: RuleToken ("var", "x") 
			   :: StringToken ":" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y") 
			   :: StringToken "}" 
			   :: SpaceToken 1
			   :: RuleToken ("lambdaast", "z") 
			   :: [], Lambda (Hidden, "x", Symb (true, "y"), Symb (true, "z"))))
     }
  :: { priority = 1;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "{"
			   :: RuleToken ("var", "x") 	    
			   :: StringToken "}"
			   :: SpaceToken 1
			   :: RuleToken ("lambdaast", "z") 
			   :: [], Lambda (Hidden, "x", Avar, Symb (true, "z"))))
     }
  :: { priority = 1;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "{"
			   :: RuleToken ("var", "x") 	    
			   :: StringToken "}"
			   :: SpaceToken 1
			   :: StringToken "->" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "z") 
			   :: [], Lambda (Hidden , "x", Avar, Symb (true, "z"))))
     }

  :: []
;;

let lambdaast_notation = {
  rule = lambdaast_notation_rules;
  errors = [];
  success = [];
}
;;

(* forall notation *)

let forallast_notation_rules =

  { priority = 0;
    ppretty = true;
    tried = [];
    ruleparser = (Deep (StringToken "("
			:: RuleToken ("var", "x") 
			:: StringToken ":" 
			:: SpaceToken 1
			:: RuleToken ("ast", "y") 
			:: StringToken ")" 
			:: StringToken "." 
			:: SpaceToken 1
			:: RuleToken ("ast", "z") 
			:: [], Forall (Explicite, "x", Symb (true, "y"), Symb (true, "z"))))
  }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "("
			   :: RuleToken ("var", "x") 
			   :: StringToken ":" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y") 
			   :: StringToken ")" 
			   :: SpaceToken 1
			   :: RuleToken ("forallast", "z") 
			   :: [], Forall (Explicite, "x", Symb (true, "y"), Symb (true, "z"))))
     }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (RuleToken ("var", "x") 	    
			   :: SpaceToken 1
			   :: RuleToken ("forallast", "z") 
			   :: [], Forall (Explicite, "x", Avar, Symb (true, "z"))))
     }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (RuleToken ("var", "x") 	    
			   :: StringToken "." 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "z") 
			   :: [], Forall (Explicite, "x", Avar, Symb (true, "z"))))
     }


  ::   { priority = 0;
	 ppretty = true;
	 tried = [];
	 ruleparser = (Deep (StringToken "["
			     :: RuleToken ("var", "x") 
			     :: StringToken ":" 
			     :: SpaceToken 1
			     :: RuleToken ("ast", "y") 
			     :: StringToken "]" 
			     :: StringToken "." 
			     :: SpaceToken 1
			     :: RuleToken ("ast", "z") 
			     :: [], Forall (Implicite, "x", Symb (true, "y"), Symb (true, "z"))))
       }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "["
			   :: RuleToken ("var", "x") 
			   :: StringToken ":" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y") 
			   :: StringToken "]" 
			   :: SpaceToken 1
			   :: RuleToken ("forallast", "z") 
			   :: [], Forall (Implicite, "x", Symb (true, "y"), Symb (true, "z"))))
     }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "["
			   :: RuleToken ("var", "x") 	    
			   :: StringToken "]"
			   :: SpaceToken 1
			   :: RuleToken ("forallast", "z") 
			   :: [], Forall (Implicite, "x", Avar, Symb (true, "z"))))
     }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "["
			   :: RuleToken ("var", "x") 	    
			   :: StringToken "]"
			   :: StringToken "." 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "z") 
			   :: [], Forall (Implicite, "x", Avar, Symb (true, "z"))))
     }


  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "{"
			   :: RuleToken ("var", "x") 
			   :: StringToken ":" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y") 
			   :: StringToken "}" 
			   :: StringToken "." 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "z") 
			   :: [], Forall (Hidden, "x", Symb (true, "y"), Symb (true, "z"))))
     }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "{"
			   :: RuleToken ("var", "x") 
			   :: StringToken ":" 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "y") 
			   :: StringToken "}" 
			   :: SpaceToken 1
			   :: RuleToken ("forallast", "z") 
			   :: [], Forall (Hidden, "x", Symb (true, "y"), Symb (true, "z"))))
     }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "{"
			   :: RuleToken ("var", "x") 	    
			   :: StringToken "}"
			   :: SpaceToken 1
			   :: RuleToken ("forallast", "z") 
			   :: [], Forall (Hidden, "x", Avar, Symb (true, "z"))))
     }
  :: { priority = 0;
       ppretty = true;
       tried = [];
       ruleparser = (Deep (StringToken "{"
			   :: RuleToken ("var", "x") 	    
			   :: StringToken "}"
			   :: StringToken "." 
			   :: SpaceToken 1
			   :: RuleToken ("ast", "z") 
			   :: [], Forall (Hidden, "x", Avar, Symb (true, "z"))))
     }

  :: []
;;

let forallast_notation = {
  rule = forallast_notation_rules;
  errors = [];
  success = [];
}
;;

(* match parser *)

let matchast_notation_rules =
  let destructor (p: 'a pparser) = 
    (tryrule (fun pb ->
		let _ = keyword "|" () pb in
		let t1 = named_parser "ast" p pb in		 
		let _ = keyword "==>" () pb in
		let t2 = named_parser "ast" p pb in		 
		  (t1, t2)
	     )
    )
  in
  { priority = 0;
    ppretty = true;
    tried = [];
    ruleparser = (Shallow (
		    (
		      fun p pb ->
			((tryrule (fun pb ->
				     let _ = keyword "match" () pb in
				     let t1 = named_parser "ast" p pb in
				     let _ = keyword "with" () pb in
				     let ldes = many (destructor p) pb in
				       Match (t1, ldes, None)
				  )
			 )
			 <|> (tryrule (fun pb ->
					 let _ = keyword "match" () pb in
					 let t1 = named_parser "ast" p pb in
					 let _ = keyword "returns" () pb in
					 let t2 = named_parser "ast" p pb in
					 let _ = keyword "with" () pb in
					 let ldes = many (destructor p) pb in
					   Match (t1, ldes, Some t2)
				      )
			     )	      
			) pb
		    ), (
		      fun p a ->
			match a with
			  | (Match (te, ldes, retty)) -> (
			      Some (
				(Verbatim "match") :: 
				  (Space 1) :: 
				  (
				    match (pparser_pprinter p te) with
				      | None -> (Verbatim "???")  
				      | Some t -> t
				  ) :: 
				  (Space 1) :: 
				  (Verbatim "returns") :: 
				  (Space 1) :: 
				  (match retty with
				     | None -> (Verbatim "???")
				     | Some ty ->
					 (
					   match (pparser_pprinter p ty) with
					     | None -> (Verbatim "???")  
					     | Some t -> t
					 )
				  ) ::
				  (Space 1) :: 
				  (Verbatim "with") :: Newline ::
				  (List.fold_left (fun acc hd ->
						       acc @ Box (
							 (Verbatim "|") :: 
							   (Space 1) :: 
							   (match (pparser_pprinter p (fst hd)) with
							      | None -> (Verbatim "???")  
							      | Some t -> t
							   ) ::
							   (Space 1) :: 
							   (Verbatim "==>") :: 
							   (Space 1) :: 
							   (match (pparser_pprinter p (snd hd)) with
							      | None -> (Verbatim "???")  
							      | Some t -> t
							   ) :: 
							   []
						       ) :: Newline :: []
						  ) [] ldes
				  )
			      )
			    )
			  | _ -> None
		    )
		  )
		 )
  }
  :: []
;;

let matchast_notation = {
  rule = matchast_notation_rules;
  errors = [];
  success = [];
}
;;



(* extension *)

let extention_notation = {
  rule = 
    { priority = 0;
      ppretty = true;
      tried = [];
      ruleparser = (Deep (RuleToken ("ast", "x") 
			  :: SpaceToken 1
			  :: StringToken "+" 
			  :: SpaceToken 1
			  :: RuleToken ("ast", "y") 
			  :: [], App ((Symb (false, "plus"))::(Symb (true, "x")):: (Symb (true, "y"))::[])))
    }
    :: []
  ;
  errors = [];
  success = [];
}
;;

let list_parser = 
  ("var", var_notation)
  :: ("ast", ast_notation)
  :: ("astunit", astunit_notation)
  :: ("lambdaast", lambdaast_notation)
  :: ("forallast", forallast_notation)
  :: ("matchast", matchast_notation)
  :: ("extention", extention_notation)
  :: []
;;

let astpparser = {
  rules = List.fold_left (fun acc hd -> VarMap.add (fst hd) (snd hd) acc) VarMap.empty list_parser;
  notations = VarSet.singleton "ast";
  rewrite = astrewrite;
  unification = astunification;
  reserved = reserved;
}
;;

let build_astpparser () = {
  rules = List.fold_left (fun acc hd -> VarMap.add (fst hd) (snd hd) acc) VarMap.empty list_parser;
  notations = VarSet.singleton "ast";
  rewrite = astrewrite;
  unification = astunification;
  reserved = reserved;
}
;;


let pprintast a =
  match pparser_pprinter astpparser a with
    | None -> printf "error printing it out!!\n"
    | Some t -> (
	let b = token2box t 80 2 in
	  printbox b
      )
;;
