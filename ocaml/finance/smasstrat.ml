(* this strat works only on close-to-close 
   with an csvbroker
*)
open Printf;;

module SMAStrat =
  struct

    type info = string;;

    type data = float list;;

    type order = int;;

    type signal = GOLONG of order
		  | GOSHORT of order
		  | CLOSE
		  | STAY
    ;;

    type status = LONG
		  | SHORT
		  | CLOSED
    ;;
		      
    type t = {
      info: string;
      smas: int list;
      mutable st: status;
    };;

    let mk s l = {
      info = s;
      smas = l;
      st = CLOSED;
    };;

    let getinfo t = t.info;;

    let rec take l n =
      match n with
	| 0 -> []
	| n -> 
	  match l with
	    | [] -> []
	    | hd::tl -> hd::(take tl (n-1))
    ;;

    let sma l n =
      if List.length l < n then None else
	Some (List.fold_left (+.) 0.0 (take l n) /. float n)
    ;;

    (*
    let ema l n =
      if List.length l < n then None else
	let alpha = 2. /. (1. +. float n) in
	Some (List.fold_right (fun hd acc -> hd *. alpha +. (acc *. (1. -. alpha))) (take l n) 0.0)
    ;;
    *)

    let rec increasing l =
      match l with
	| [] -> true
	| hd::tl -> increasing' hd tl
    and increasing' e l =
      match l with
	| [] -> true
	| hd::tl -> hd > e && increasing' hd tl
    ;;

    let rec decreasing l =
      match l with
	| [] -> true
	| hd::tl -> decreasing' hd tl
    and decreasing' e l =
      match l with
	| [] -> true
	| hd::tl -> hd < e && decreasing' hd tl
    ;;

    let proceedData self data =
      let l = List.map (fun hd -> sma (List.rev data) hd) self.smas in
      let l = List.fold_right (fun hd acc ->
	match (hd, acc) with
	  | (Some hd, Some tl) -> Some (hd::tl)
	  | _ -> None
      ) l (Some []) in
      match l with
	| None -> STAY
	| Some l ->
	  (*printf "[%s]\n" (String.concat ", " (List.map string_of_float l));*)
	  match self.st with
	    | LONG when not (increasing l) -> (*printf "[%s] " (String.concat ", " (List.map string_of_float l));*) CLOSE
	    | SHORT when not (decreasing l) -> (*printf "[%s] " (String.concat ", " (List.map string_of_float l));*) CLOSE
	    | CLOSED when increasing l -> (*printf "[%s] " (String.concat ", " (List.map string_of_float l));*) GOLONG 1
	    | CLOSED when decreasing l -> (*printf "[%s] " (String.concat ", " (List.map string_of_float l));*) GOSHORT (-1)
	    | _ -> STAY
    ;;


    let setstatus t status = t.st <- status;;      
    
  end;;
