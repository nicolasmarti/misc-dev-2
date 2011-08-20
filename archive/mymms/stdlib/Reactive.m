Open StdLib.Reactive.

Require Option.
Require Prod.

Inductive Reactive :=
| isReactive:
  V (Input: Type). 
  V (Output: Type). 
  V (State: Type). 
  V (st: State).
  V (strategy: Input -> State -> prod (option Output) State).
      Reactive.

Definition Input r :=
  match r with
    | isReactive i _ _ _ _ ==> i.

Definition Output r :=
  match r with
    | isReactive _ o _ _ _ ==> o.

Definition State r :=
  match r with
    | isReactive _ _ s _ _ ==> s.

Definition state r : State r :=
  match r with
    | isReactive _ _ _ st _ ==> st.

Definition strategy r : Input r -> State r -> prod (option (Output r)) (State r) :=
  match r with
    | isReactive _ _ _ _ strat ==> strat.

Definition run r (i: Input r) : prod (option (Output r)) Reactive := 
  match r with
    | isReactive _ _ _ st strat ==> (
      	  match (strat i st) with
	    | pair o st ==> 
	             pair o (isReactive _ _ _ st strat)
).

Definition residualreactive r (res: prod (option (Output r)) Reactive) :=
   match res with
     | pair o r ==> r
.

Definition residualoutput r (res: prod (option (Output r)) Reactive) :=
   match res with
     | pair o r ==> o
.

Close.
