open Llvm;;
open Llvm_executionengine;;
open Llvm_target;;
open Llvm_scalar_opts;;
open Varmap;;
open Varset;;

open Array;;
open Mllvm;;

open Printf;;

let (cos, costy) = compile_block0 comp_st (
  Extern ("cos", [|(TDouble, "x")|], TDouble)
);;

let (rand, randty) = compile_block0 comp_st (
  Extern ("rand", [||], TDouble)
);;

let (exp, expty) = compile_block0 comp_st (
  Extern ("exp", [| (TDouble, "x") |], TDouble)
);;

let (sqrt, sqrty) = compile_block0 comp_st (
  Extern ("sqrt", [| (TDouble, "x") |], TDouble)
);;

let (pow, powty) = compile_block0 comp_st (
  Extern ("pow", [| (TDouble, "x"); (TDouble, "y") |], TDouble)
);;

let (americanPut, americanPutTy) = compile_block0 comp_st (
  Fct ("americanPut",
       [| (TDouble, "T"); (TDouble, "S"); (TDouble, "K"); (TDouble, "r"); (TDouble, "sigma"); (TDouble, "q"); (TInteger 32, "n") |],
       TDouble,
       Let ([| 
	      (* deltaT:= T/ n;  *) 
	      ("deltaT", EBop (Div, EVar "T", ECast (TDouble, EVar "n")));
	      (* up:=     exp(sigma* sqrt(deltaT)); *)
	      ("up", ECall (EVar "exp", [| EBop (Mul, 
						 EVar "sigma",
						 ECall (EVar "sqrt", [| EVar "deltaT" |])
						) |]));
	      (* p0:=     (up* exp(-r* deltaT)- exp(-q* deltaT))* up/ (up^ 2- 1); *)
	      ("p0", EBop (Div,
			   EBop (Mul,
				 EBop (Sub,
				       EBop (Mul,
					     EVar "up",
					     ECall (EVar "exp", [| EBop (Mul, EUop (Neg, EVar "r"), EVar "deltaT") |])
					    ),
				       ECall (EVar "exp", [| EBop (Mul, EUop (Neg, EVar "q"), EVar "deltaT") |])
				      ),
				 EVar "up"
				),
			   EBop (Sub,
				 ECall (EVar "pow", [| EVar "up"; ECste (CDouble 2.)|]),
				 ECste (CDouble 1.)
				)
			  )
	      );
	      (* p1:=     exp(-r* deltaT)- p0; *)
	      ("p1", EBop (Sub,
			   ECall (EVar "exp", [| EBop (Mul, EUop (Neg, EVar "r"), EVar "deltaT") |]),
			   EVar "p0"
			  )
	      );
	      (* p := array n ??? need something to build with expr *)
	      (*("p2", ECste (CRef (CNull (TArray (100, TDouble)))));*)
	      ("p", EArray (TDouble, EVar "n"))
	      (*("p20", ENth (ECste (CInt (32, 0)), EVar "p2"))*)
	    |],
	    Seq ([| 
		   (*
		     for i:= 0 to n {                         ' initial values at time T
		     p(i):= K- S* up^(2* i- n); if p(i)< 0 then p(i)=0;
		     }*)
		   Let ([| ("i", ECste (CRef (CInt (32, 0)))) |],
			Seq (
			  [| While (BLeq (ERef (EVar "i"), EVar "n"),
				    Seq ([| Assign (LNth (EVar "p", ERef (EVar "i")), 
						    EBop (Sub,
							  EVar "K",
							  EBop (Mul,
								EVar "S",
								ECall (EVar "pow", [| EVar "up"; ECast (TDouble, EBop (Sub, EBop(Mul, ECste (CInt (32, 2)), ERef (EVar "i")), EVar "n"))|])
							       )
							 )
						   );
					    If (BLt (ENth (ERef (EVar "i"), EVar "p"), ECste (CDouble 0.)),
						Assign (LNth (EVar "p", ERef (EVar "i")), ECste (CDouble 0.))
					    );
					    Assign (LVar "i", EBop (Add, ERef (EVar "i"), ECste (CInt (32, 1))))
					      
					 |],
					 None
					)
				   );			  
			     Let ([| ("j", EDeref (EBop (Sub, EVar "n", ECste (CInt (32, 1))))) |],
				  While (BGeq (ERef (EVar "j"), ECste (CInt (32, 0))),
					 Seq ([| Assign (LVar "i", ECste (CInt (32, 0)));
						 While (BLeq (ERef (EVar "i"), ERef (EVar "j")),
							Seq ([| Assign (LNth (EVar "p", ERef (EVar "i")),
									EBop (Add,
									      EBop(Mul, EVar "p0", ENth (ERef (EVar "i"), EVar "p")),
									      EBop(Mul, EVar "p1", ENth (EBop (Add, ECste (CInt (32, 1)), ERef (EVar "i")), EVar "p"))
									     )
								       )
							     ; Let ([| ("exc", 
									EBop (Sub,
									      EVar "K",
									      EBop (Mul,
										    EVar "S",
										    ECall (EVar "pow", [| EVar "up"; ECast (TDouble, EBop (Sub, EBop(Mul, ECste (CInt (32, 2)), ERef (EVar "i")), ERef (EVar "j")))|])
										   )
									     )
								       )
								    |],
								    If (BLt (ENth (ERef (EVar "i"), EVar "p"),
									     EVar "exc"
									    ),
									Assign (LNth (EVar "p", ERef (EVar "i")), 
										EVar "exc"
									       )
								       )
								    
								   )
							     ; Assign (LVar "i", EBop (Add, ERef (EVar "i"), ECste (CInt (32, 1))))
							     |],
							     None
							    )
						       );
						 Assign (LVar "j", EBop (Sub, ERef (EVar "j"), ECste (CInt (32, 1))))
					      |],
					      None
					     )
					)
				 )
			  |], None
			)
		       )
		 |],
		 (* return americanPut:= p(0); *)
		 Some (ENth (ECste (CInt (16, 0)), EVar "p"))
		)
	   )
      )
);;

			  (*
			    for j:= n- 1 to 0 step -1 {              ' move to earlier times
			    for i:= 0 to j {
		            p(i):= p0* p(i)+ p1* p(i+1);     ' binomial value
		            exercise:= K- S* up^ (2* i- j);  ' exercise value
		            if p(i)< exercise then p(i)= exercise;
			    }    
			    }
			  *)

dump_module comp_st.modul;;

(* T S K r sigma q n *)

let result = ExecutionEngine.run_function americanPut 
  [| GenericValue.of_float (build_llvmtype comp_st VarMap.empty TDouble) 255.;
     GenericValue.of_float (build_llvmtype comp_st VarMap.empty TDouble) 100.;
     GenericValue.of_float (build_llvmtype comp_st VarMap.empty TDouble) 100.;
     GenericValue.of_float (build_llvmtype comp_st VarMap.empty TDouble) 0.02;
     GenericValue.of_float (build_llvmtype comp_st VarMap.empty TDouble) 0.2;
     GenericValue.of_float (build_llvmtype comp_st VarMap.empty TDouble) 0.;
     GenericValue.of_int (build_llvmtype comp_st VarMap.empty (TInteger 32)) 1000
  |] comp_st.engine;;

print_string "main Evaluated to ";
print_float (GenericValue.as_float (build_llvmtype comp_st VarMap.empty TDouble) result);;
print_newline ();;

open Mllvmpparser;;
open Parser;;
open Pprinter;;

let stream_of_string s =
  Stream.from
    (fun x ->
       match x with
	 | 0 -> Some s
	 | _ -> None
    )

let text1 = "i8";;
let lines1 = stream_of_string text1;;
let pb1 = build_parserbuffer lines1;;

try 
  let mexpr = llvmtype_parser pb1 in
    printf "%s\n" text1;
    printbox (token2box (llvmtype_pprinter VarMap.empty mexpr) 100 4);
    printf "\n\n";
with
  | NoMatch -> 
      printf "error:%s\n\n" (errors2string pb1);
      printf "%s\n\n" (markerror pb1);
;;

let text2 = "()";;
let lines2 = stream_of_string text2;;
let pb2 = build_parserbuffer lines2;;

try 
  let mexpr = cmd0_parser pb2 in
    printf "%s\n" text2;
    printbox (token2box (cmd0_pprinter mexpr false) 100 4);
    printf "\n\n";
with
  | NoMatch -> 
      printf "error:%s\n\n" (errors2string pb2);
      printf "%s\n\n" (markerror pb2);
;;
