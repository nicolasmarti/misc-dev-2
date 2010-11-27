open Llvm;;
open Llvm_executionengine;;
open Llvm_target;;
open Llvm_scalar_opts;;
open Varmap;;
open Varset;;

open Array;;

open Printf;;

open Set;;
open Map;;

(**************************************************************)

ignore (initialize_native_target ());;


(**************************************************************)

type llvmtype = TUnit
		| TInteger of int
		| TFloat
		| TDouble
		| TQuad
		| TBool
		| TString
		| TFct of llvmtype array * llvmtype
		| TPtr of llvmtype
		| TTuple of llvmtype array
		| TVector of int * llvmtype
		| TArray of int * llvmtype
		| TDynArray of llvmtype
		| TUnknownp
		| TVar of string
		| TCste of lltype
		| TAVar
		| TGC of llvmtype
;;

let rec llvmtype_compare (t1: llvmtype) (t2: llvmtype) : int =
  if (t1 < t2) then
    -1 
  else if (t1 > t2) then 1 else 0
;;

module Orderedllvmtype = 
    struct
      type t = llvmtype
      let compare x y = llvmtype_compare x y
    end;;

module LlvmtypeSet = Set.Make(Orderedllvmtype);; 
module LlvmtypeMap = Map.Make(Orderedllvmtype);; 

module OrderedInt = 
    struct
      type t = int
      let compare x y = if (x<y) then -1 else if (x>y) then 1 else 0
    end;;

module IntSet = Set.Make(OrderedInt);; 
module IntMap = Map.Make(OrderedInt);; 


type bop = Add 
	  | Sub
	  | Mul
	  | Div
;;

type uop = Neg
;;

type cste = CInt of int * int
	    | CBool of bool
	    | CFloat of float
	    | CDouble of float
	    | CTuple of cste array
	    | CArray of cste array
	    | CVector of cste array
	    | CBop of bop * cste * cste
	    | CUop of uop * cste
	    (* A -> ref A*)
	    | CRef of cste
	    | CNull of llvmtype
	    | CValue of llvalue * llvmtype
;;

type expr0 = ECste of cste 
	     | EVar of string
	     (* A -> Ref A *)
	     | EDeref of expr0
	     (* ref A -> A *)
	     | ERef of expr0
	     | ENth of expr0 * expr0
	     | EBop of bop * expr0 * expr0
	     | EUop of uop * expr0
	     | ECast of llvmtype * expr0
	     | ECall of expr0 * expr0 array
	     | EArray of llvmtype * expr0
;;

type bexpr0 = BCste of bool
	      | BVar of string
	      | BEq of expr0 * expr0
	      | BLt of expr0 * expr0
	      | BGt of expr0 * expr0
	      | BLeq of expr0 * expr0
	      | BGeq of expr0 * expr0
	      | BNeg of bexpr0
	      | BAnd of bexpr0 * bexpr0
;;

type lvalue = LVar of string
	      | LNth of expr0 * expr0
;;

type cmd0 = Let of (string * expr0) array * cmd0
	  | If of bexpr0 * cmd0
	  | Ifte of bexpr0 * cmd0 * cmd0
	  | While of bexpr0 * cmd0
	  | Switch of expr0 * (cste * cmd0) array * cmd0
	  | Seq of cmd0 array * expr0 option
	  (* ref A -> A -> () *)
	  | Assign of lvalue * expr0
	  | Value of expr0
	  | Return of expr0
	  | Unit
;;

type block0 = Extern of string * (llvmtype * string) array * llvmtype
	      | Fct of string * (llvmtype * string) array * llvmtype * cmd0
	      | Expr of string * cmd0 * llvmtype
	      | GCste of string * cste
	      | Global of string * cste
;;

(**************************************************************)

type compile_state =
    { mutable ctxt: llcontext;
      mutable modul: llmodule;
      mutable builder: llbuilder;
      mutable typeenv: llvmtype VarMap.t;
      mutable valueenv: (llvalue * llvmtype) VarMap.t;
      mutable engine: ExecutionEngine.t;
      mutable passmng: [`Function] PassManager.t;
      mutable optimize: bool;
      mutable gc_typeset: IntSet.t;
      mutable gc_typemap: int LlvmtypeMap.t;
    }
;;


let rec build_llvmtype (gst: compile_state) (lst: lltype VarMap.t) (ty: llvmtype) : lltype =
  match ty with
    | TUnit -> void_type gst.ctxt
    | TInteger i -> integer_type gst.ctxt i
    | TFloat -> float_type gst.ctxt
    | TDouble -> double_type gst.ctxt
    | TQuad -> fp128_type gst.ctxt
    | TBool -> integer_type gst.ctxt 1
    | TString -> pointer_type (integer_type gst.ctxt 8)
    | TFct (args, ret) -> 
	let ret = build_llvmtype gst lst ret in
	let args = Array.map (fun hd -> build_llvmtype gst lst hd) args in
	  function_type ret args
    | TPtr ty -> pointer_type (build_llvmtype gst lst ty)
    | TTuple tys -> 
	let tys = Array.map (fun hd -> build_llvmtype gst lst hd) tys in
	  struct_type gst.ctxt tys
    | TVector (i, ty) ->
	vector_type (build_llvmtype gst lst ty) i
    | TArray (i, ty) ->
	array_type (build_llvmtype gst lst ty) i
    | TDynArray ty ->
	pointer_type (struct_type gst.ctxt [| i32_type gst.ctxt; array_type (build_llvmtype gst lst ty) 0|])
    | TUnknownp ->
	pointer_type (i8_type gst.ctxt)
    | TVar v -> (
	try 
	  VarMap.find v lst
	with
	  | _ -> 
	      try
		build_llvmtype gst lst (VarMap.find v gst.typeenv)
	      with
		| e -> 
		    printf "Can't find type variable %s\n" v;
		    raise e
      )
    | TCste ty -> ty
    | TGC ty -> pointer_type (struct_type gst.ctxt [| i32_type gst.ctxt; build_llvmtype gst lst ty|])
	
;;

let comp_st = 
  let c = global_context () in 
  let m = create_module c "main" in 
  let eng = ExecutionEngine.create m in 
  let pm = PassManager.create_function m in

    TargetData.add (ExecutionEngine.target_data eng) pm;
    
    (* optimizations *)

    add_constant_propagation pm;
    add_sccp pm;
    add_dead_store_elimination pm;
    add_aggressive_dce pm;
    add_scalar_repl_aggregation pm;
    add_ind_var_simplification pm;    
    add_instruction_combination pm;
    add_licm pm;
    add_loop_unswitch pm;
    add_loop_unroll pm;
    add_loop_rotation pm;
    add_loop_index_split pm;
    add_memory_to_register_promotion pm;
    add_memory_to_register_demotion pm;
    add_reassociation pm;
    add_jump_threading pm;
    add_cfg_simplification pm;
    add_tail_call_elimination pm;
    add_gvn pm;
    add_memcpy_opt pm;
    add_loop_deletion pm;
    add_lib_call_simplification pm;

    (* init passmanager *)
    ignore (PassManager.initialize pm);

    let st = {
      ctxt = c;
      modul = m;
      builder = builder c;
      typeenv = VarMap.empty;
      valueenv = VarMap.empty;
      engine = eng;
      passmng = pm;
      optimize = false;
      gc_typeset = IntSet.empty;
      gc_typemap = LlvmtypeMap.empty;      
    } in
      (* grabbing some function *)
    let malloc_ty = TFct ([| TInteger 32 |], TPtr (TInteger 8)) in
    let malloc_llvmty = (build_llvmtype st VarMap.empty malloc_ty) in
    let malloc_f = declare_function "malloc" malloc_llvmty st.modul in
      st.valueenv <- VarMap.add "__malloc_" (malloc_f, malloc_ty) st.valueenv;
      let free_ty = TFct ([| TPtr (TInteger 8) |], TUnit) in
      let free_llvmty = (build_llvmtype st VarMap.empty free_ty) in
      let free_f = declare_function "free" free_llvmty st.modul in
	st.valueenv <- VarMap.add "__free_" (free_f, free_ty) st.valueenv;
	let memcpy_ty = TFct ([| TPtr (TInteger 8); TPtr (TInteger 8); (TInteger 32) |], TPtr (TInteger 8)) in
	let memcpy_llvmty = (build_llvmtype st VarMap.empty memcpy_ty) in
	let memcpy_f = declare_function "memcpy" memcpy_llvmty st.modul in
	  st.valueenv <- VarMap.add "__memcpy_" (memcpy_f, memcpy_ty) st.valueenv;
	  st
;;

(**************************************************************)


let rec reg_llvmtype (gst: compile_state) (l: (string * llvmtype) list) : llvalue list =
  let (ln, lt) = List.split l in

  let lnt = List.map (fun hd -> 
			let ty = opaque_type gst.ctxt in
			let op = handle_to_type ty in
			  (hd, ty, op)
		     ) ln in

  let lst = List.fold_left (fun acc (hd1, hd2, hd3) -> 
			      VarMap.add hd1 hd2 acc
			 ) VarMap.empty lnt in

  let lt = List.map (build_llvmtype gst lst) lt in

  let _ = List.map (fun (hd1, (hd2, hd3, hd4)) -> refine_type hd3 hd1) (List.combine lt lnt) in

  let new_tys = List.map (fun (_, _, op) -> type_of_handle op) lnt in

  let new_vals = List.map (fun (hd1, (hd2, hd3, hd4)) -> declare_global hd1 hd2 gst.modul) (List.combine new_tys lnt) in
    
    gst.valueenv <- List.fold_left (fun acc ((hd1, hd2), hd3) -> 
				      VarMap.add hd1 (hd3, hd2) acc
				   ) gst.valueenv (List.combine l new_vals) ;

    gst.typeenv <- List.fold_left (fun acc (hd1, hd2) -> 
				      VarMap.add hd1 hd2 acc
				   ) gst.typeenv l;

    new_vals
    
;;

(* this function encode the dynamic computation of sizeof *)

let sizeof (gst: compile_state) (ty: llvmtype) : llvalue =
  let one = (const_int (integer_type gst.ctxt 32) 1) in
  let zero = (const_int (integer_type gst.ctxt 32) 0) in
  let addr = const_bitcast zero (build_llvmtype gst VarMap.empty (TPtr ty)) in
  let sizeo = build_gep addr [| one |] "size" gst.builder in
    build_bitcast sizeo (integer_type gst.ctxt 32) "cast" gst.builder
;;

(* garbage collection *)

Random.self_init ();;

let create_type_id (gst: compile_state) (ty: llvmtype) : int =
  try 
    LlvmtypeMap.find ty gst.gc_typemap
  with
    | Not_found ->
	let b = ref false in
	let tyval = ref 0 in
	while !b do
	  tyval := (Random.int 65000);
	  b := not (IntSet.mem !tyval gst.gc_typeset);
	  if !b then (
	    gst.gc_typeset <- IntSet.add !tyval gst.gc_typeset;
	    gst.gc_typemap <- LlvmtypeMap.add ty !tyval gst.gc_typemap;
	  );	    
	done;
	  !tyval
;;

let rec grab_firstlevel_gc (gst: compile_state) (b: llbuilder) (ty: llvmtype) (curp: llvalue) : unit =
  match ty with
    | TUnit -> ()
    | TInteger i -> ()
    | TFloat -> ()
    | TDouble -> ()
    | TQuad -> ()
    | TBool -> ()
    | TString -> ()
    | TFct (args, ret) -> ()
    | TPtr ty -> ()
    | TTuple tys -> (
	Array.iteri (
	  fun i hd ->
	    let curp' = build_struct_gep curp i "tuplelookup" b in
	      grab_firstlevel_gc gst b hd curp'
	) tys
      )
    | TVector _ -> ()
    | TArray (i, ty) -> (
	let j = ref 0 in
	  while (!j < i) do
	    let curp' = build_struct_gep curp !j "tuplelookup" b in
	      grab_firstlevel_gc gst b ty curp';
	      j := !j + 1;
	  done;	  
      )
    | TDynArray ty -> (
	raise (Failure "Not Yet Implemented")
      )
    | TUnknownp -> ()
    | TVar v -> ()
    | TCste t -> ()
    | TAVar -> ()
    | TGC ty -> (
	
	let grab = gc_codegen_grab gst ty in
	let _ = build_call grab [| curp |] "grab-first-level" b in
	  ()
      )
and gc_codegen_create (gst: compile_state) (ty: llvmtype) : llvalue =
  let fctname = String.concat "" ["__"; string_of_int (create_type_id gst ty); "_GC_create"] in
    match lookup_function fctname gst.modul with
      | Some f -> f
      | None -> 
	  
	  let builder = builder gst.ctxt in
	  let fty = TFct ([| TPtr (TGC ty) |], TPtr (TTuple [| TInteger 32; ty|])) in
	  let llvmfty = (build_llvmtype gst VarMap.empty fty) in
	  let f = declare_function fctname llvmfty gst.modul in
	  let _ = set_value_name "ref" (params f).(0) in
	  let entryb = append_block gst.ctxt "entry" f in
	    position_at_end entryb builder;
	    
	    let size1 = sizeof gst ty in

	    let size2 = sizeof gst (TGC ty) in
	      
	    let mem = build_call (fst (VarMap.find "__malloc_" gst.valueenv)) [| size2 |] "memalloc" builder in

	    let addr = build_bitcast mem (build_llvmtype gst VarMap.empty (TPtr ty)) "cast" builder in

	    let one = const_int (integer_type gst.ctxt 32) 1 in
	    let zero = const_int (integer_type gst.ctxt 32) 0 in

	    let counter = build_gep addr [| zero; zero |] "counter" builder in
	    let _ = build_gep addr [| zero; one |] "data" builder in

	    let _ = build_store zero counter builder in

	    let _ = build_call (fst (VarMap.find "__memcpy_" gst.valueenv)) [| mem; (params f).(0); size1 |] "memcpy" builder in

	      grab_firstlevel_gc gst builder ty addr;	    
	      build_ret addr builder;

and gc_codegen_grab (gst: compile_state) (ty: llvmtype) : llvalue =
  raise (Failure "Not Yet Implemented")
and gc_codegen_drop (gst: compile_state) (ty: llvmtype) : llvalue =
  raise (Failure "Not Yet Implemented")
and gc_codegen_delete (gst: compile_state) (ty: llvmtype) : llvalue =
  raise (Failure "Not Yet Implemented")
;;
    

(**************************************************************)
  
let compile_cbop (gst: compile_state) (op: bop) (v1: llvalue) (v2: llvalue) (ty: llvmtype) : (llvalue * llvmtype) =
  match op with
    | Add -> (
	match ty with
	  | TInteger _ | TVector (_, TInteger _) -> (
	      (const_add v1 v2, ty)
	    )
	  | TDouble | TFloat | TVector (_, TFloat) | TVector (_, TDouble) -> (
	      (const_fadd v1 v2, ty)
	    )
	  | _ -> raise (Failure "Wrong type for Add")
      )
    | Sub -> (
	match ty with
	  | TInteger _ | TVector (_, TInteger _) -> (
	      (const_sub v1 v2, ty)
	    )
	  | TFloat | TVector (_, TFloat) | TDouble | TVector (_, TDouble) -> (
	      (const_fsub v1 v2, ty)
	    )
	  | _ -> raise (Failure "Wrong type for Sub")
      )
    | Mul -> (
	match ty with
	  | TInteger _ | TVector (_, TInteger _) -> (
	      (const_mul v1 v2, ty)
	    )
	  | TFloat | TVector (_, TFloat) | TDouble | TVector (_, TDouble) -> (
	      (const_fmul v1 v2, ty)
	    )
	  | _ -> raise (Failure "Wrong type for Mul")
      )
    | Div -> (
	match ty with
	  | TInteger _ | TVector (_, TInteger _) -> (
	      (const_sdiv v1 v2, ty)
	    )
	  | TFloat | TVector (_, TFloat) | TDouble | TVector (_, TDouble) -> (
	      (const_fdiv v1 v2, ty)
	    )
	  | _ -> raise (Failure "Wrong type for Div")
      )
;;

let compile_cuop (gst: compile_state) (op: uop) (v: llvalue) (ty: llvmtype) : (llvalue * llvmtype) =
  match op with
    | Neg -> (
	match ty with
	  | TInteger _ -> (const_neg v, ty)
	  | TFloat | TDouble -> (const_fneg v, ty)
      )
;;


let compile_bop (gst: compile_state) (op: bop) (v1: llvalue) (v2: llvalue) (ty: llvmtype) : (llvalue * llvmtype) =
  match op with
    | Add -> (
	match ty with
	  | TInteger _ | TVector (_, TInteger _) -> (
	      (build_add v1 v2 "addtmp" gst.builder, ty)
	    )
	  | TFloat | TVector (_, TFloat) | TDouble | TVector (_, TDouble) -> (
	      (build_fadd v1 v2 "addtmp" gst.builder, ty)
	    )
	  | _ -> raise (Failure "Wrong type for Add")
      )
    | Sub -> (
	match ty with
	  | TInteger _ | TVector (_, TInteger _) -> (
	      (build_sub v1 v2 "subtmp" gst.builder, ty)
	    )
	  | TFloat | TVector (_, TFloat) | TDouble | TVector (_, TDouble) -> (
	      (build_fsub v1 v2 "subtmp" gst.builder, ty)
	    )
	  | _ -> raise (Failure "Wrong type for Sub")
      )
    | Mul -> (
	match ty with
	  | TInteger _ | TVector (_, TInteger _) -> (
	      (build_mul v1 v2 "multmp" gst.builder, ty)
	    )
	  | TFloat | TVector (_, TFloat) | TDouble | TVector (_, TDouble) -> (
	      (build_fmul v1 v2 "multmp" gst.builder, ty)
	    )
	  | _ -> raise (Failure "Wrong type for Mul")
      )
    | Div -> (
	match ty with
	  | TInteger _ | TVector (_, TInteger _) -> (
	      (build_sdiv v1 v2 "divtmp" gst.builder, ty)
	    )
	  | TFloat | TVector (_, TFloat) | TDouble | TVector (_, TDouble) -> (
	      (build_fdiv v1 v2 "divtmp" gst.builder, ty)
	    )
	  | _ -> raise (Failure "Wrong type for Div")
      )
;;

let compile_uop (gst: compile_state) (op: uop) (v: llvalue) (ty: llvmtype) : (llvalue * llvmtype) =
  match op with
    | Neg -> (
	match ty with
	  | TInteger _ -> (build_neg v "negtmp" gst.builder, ty)
	  | TFloat | TDouble -> (build_fneg v "negtmp" gst.builder, ty)
      )
;;


let rec compute_cste (gst: compile_state) (c: cste) : (llvalue * llvmtype) =
  match c with
    | CInt (sz, v) -> (const_int (integer_type gst.ctxt sz) v, TInteger sz)
    | CBool b -> (const_int (i1_type gst.ctxt) (if b then 1 else 0), TBool)
    | CFloat f -> (const_float (float_type gst.ctxt) f, TFloat)
    | CDouble f -> (const_float (double_type gst.ctxt) f, TDouble)
    | CArray a -> (
	let a = Array.map (compute_cste gst) a in
	let vs = Array.map fst a in
	let tys = Array.map snd a in
	let ty = tys.(0) in
	  if (Array.fold_left (fun acc hd -> hd = ty && acc) true tys) then (
	    (const_array (build_llvmtype gst VarMap.empty ty) vs, TArray (Array.length a, ty))
	  ) else (
	    raise (Failure "Array: not homogeneous type")
	  )
      )
    | CTuple t -> (
	let t = Array.map (compute_cste gst) t in
	let vs = Array.map fst t in
	let tys = Array.map snd t in
	(const_struct gst.ctxt vs,
	 TTuple tys	 
	)
      )
    | CVector v -> (
	let v = Array.map (compute_cste gst) v in
	let vs = Array.map fst v in
	let tys = Array.map snd v in
	let ty = tys.(0) in
	  if (Array.fold_left (fun acc hd -> hd = ty && acc) true tys) then (
	    (const_vector  vs, TVector (Array.length v, ty))
	  ) else (
	    raise (Failure "Array: not homogeneous type")
	  )
      )
    | CBop (op, c1, c2) -> (
	let (v1, t1) = compute_cste gst c1 in
	let (v2, t2) = compute_cste gst c2 in
	  compile_cbop gst op v1 v2 t1
      )   
    | CUop (op, c) -> (
	let (v, t) = compute_cste gst c in
	  compile_cuop gst op v t
      )   
    | CRef c -> (
	let (v, t) = compute_cste gst c in
	let var = build_alloca (build_llvmtype gst VarMap.empty t) "cref" gst.builder in
	  ignore (build_store v var gst.builder);
	  (var, TPtr t)
	
      )
    | CNull ty -> (
	(const_null (build_llvmtype gst VarMap.empty ty), ty)
      )
    | CValue (v, ty) -> (
	(v, ty)
      )
;;


let rec compile_expr0 (gst: compile_state) (e: expr0) : (llvalue * llvmtype) =
  match e with
    | ECste c -> compute_cste gst c
    | EVar s -> (
	try
	  VarMap.find s gst.valueenv
	with 
	  | e -> printf "can't find variable %s\n" s; raise e
      )
    | ERef e -> (
	let (v, t) = compile_expr0 gst e in
	  match t with
	    | TPtr ty -> (
		(build_load v "load" gst.builder, ty)
	      )
	    | _ -> raise (Failure "no pointer")
      )
    | EDeref c -> (
	let (v, t) = compile_expr0 gst c in
	let var = build_alloca (build_llvmtype gst VarMap.empty t) "ederef" gst.builder in
	  ignore (build_store v var gst.builder);
	  (var, TPtr t)	
      )
    | ENth (i, e) -> (
	let (iv, it) = compile_expr0 gst i in
	let (ev, et) = compile_expr0 gst e in
	let zero = const_int (integer_type gst.ctxt 32) 0 in
	let one = const_int (integer_type gst.ctxt 32) 1 in
	  match et with
	    | TPtr (TArray (i, ty)) -> (
		
		let ptr = build_gep ev [| zero; iv |] "arraylookup" gst.builder in
		  (build_load ptr "load" gst.builder, ty)

	      )
	    | (TDynArray ty) -> (
		
		let ptr = build_gep ev [| zero; one; iv |] "arraylookup" gst.builder in
		  (build_load ptr "load" gst.builder, ty)

	      )
	    | TPtr (TTuple tys) -> (

		  match i with
		    | ECste (CInt (n, i)) ->
			let ptr = build_struct_gep ev i "tuplelookup" gst.builder in
			  (build_load ptr "load" gst.builder, tys.(i))
			    
		    | _ -> raise (Failure "tuple lookup only for constante")
			
	      )
	    | TVector (i, ty) -> (
		
		(build_extractelement ev iv "vector extract" gst.builder, ty)

	      )
	    | TPtr ty -> (
		let ptr = build_gep ev [| iv |] "ptrlookup" gst.builder in
		  (build_load ptr "load" gst.builder, ty)
	      )
	    | _ -> raise (Failure "Wrong type for lookup")

      )
    | EBop (b, e1, e2) ->
	let (v1, t1) = compile_expr0 gst e1 in
	let (v2, t2) = compile_expr0 gst e2 in
	  compile_bop gst b v1 v2 t1
    | EUop (b, e) ->
	let (v, t) = compile_expr0 gst e in
	  compile_uop gst b v t
    | ECast (toty, e) -> (
	let (v, fromty) = compile_expr0 gst e in
	  match (fromty, toty) with
	    | (TInteger n1, TInteger n2) -> (
		(build_trunc v (build_llvmtype gst VarMap.empty toty) "convtmp" gst.builder, toty)
	      )
	    | (TInteger _, TFloat) ->(
		(build_sitofp v (build_llvmtype gst VarMap.empty toty) "convtmp" gst.builder, toty)
	      )
	    | (TInteger _, TDouble) ->(
		(build_sitofp v (build_llvmtype gst VarMap.empty toty) "convtmp" gst.builder, toty)
	      )
	    | _ -> raise (Failure "unknown conversion")
      )
    | ECall (f, args) -> (
	let (fv, fty) = compile_expr0 gst f in
	let (argsv, argsty) = List.split (Array.to_list (Array.map (compile_expr0 gst) args)) in
	  match fty with
	    | TPtr (TFct (args, ret)) -> (
		(build_call fv (Array.of_list argsv) "fctcalltmp" gst.builder, ret)
	      )
	    | _ -> raise (Failure "Error: bad function ptr type")

      )
	(* This is not really what I intend to do ... *)
    | EArray (ty, e) -> (
	let (v, t) = compile_expr0 gst e in
	let mty = (build_llvmtype gst VarMap.empty ty) in
	  (build_array_alloca mty v "dynarray" gst.builder, TPtr ty)
      )
;;

let rec compile_bexpr0 (gst: compile_state) (b: bexpr0) : (llvalue * llvmtype) =
  match b with
    | BCste b -> (
	(const_int (i1_type gst.ctxt) (if b then 1 else 0), TBool)
      )
    | BVar s -> (
	try
	  VarMap.find s gst.valueenv
	with
	  | e -> printf "can't find variable %s\n" s; raise e
      )
    | BEq (e1, e2) -> (
	let (v1, t1) = compile_expr0 gst e1 in
	let (v2, t2) = compile_expr0 gst e2 in
	  match t1 with
	    | TInteger _ | TPtr _ -> ( 
		(build_icmp Icmp.Eq v1 v2 "icmptmp" gst.builder, TBool)
	      )
	    | TVector (n, TInteger _) -> (
		(build_icmp Icmp.Eq v1 v2 "icmptmp" gst.builder, TVector (n, TBool))
	      )
	    | TFloat -> ( 
		(build_fcmp Fcmp.Oeq v1 v2 "fcmptmp" gst.builder, TBool)
	      )
	    | TVector (n, TFloat) -> (
		(build_fcmp Fcmp.Oeq v1 v2 "fcmptmp" gst.builder, TVector (n, TBool))
	      )
	    | _ -> raise (Failure "(1)Not Yet implemented")
      )
    | BLt (e1, e2) -> (
	let (v1, t1) = compile_expr0 gst e1 in
	let (v2, t2) = compile_expr0 gst e2 in
	  match t1 with
	    | TInteger _ | TPtr _ -> ( 
		(build_icmp Icmp.Slt v1 v2 "icmptmp" gst.builder, TBool)
	      )
	    | TVector (n, TInteger _) -> (
		(build_icmp Icmp.Slt v1 v2 "icmptmp" gst.builder, TVector (n, TBool))
	      )
	    | TFloat | TDouble -> ( 
		(build_fcmp Fcmp.Olt v1 v2 "fcmptmp" gst.builder, TBool)
	      )
	    | TVector (n, TFloat) | TVector (n, TDouble) -> (
		(build_fcmp Fcmp.Olt v1 v2 "fcmptmp" gst.builder, TVector (n, TBool))
	      )
	    | _ -> raise (Failure "(2)Not Yet implemented")
      )
    | BGt (e1, e2) -> (
	let (v1, t1) = compile_expr0 gst e1 in
	let (v2, t2) = compile_expr0 gst e2 in
	  match t1 with
	    | TInteger _ | TPtr _ -> ( 
		(build_icmp Icmp.Sgt v1 v2 "icmptmp" gst.builder, TBool)
	      )
	    | TVector (n, TInteger _) -> (
		(build_icmp Icmp.Sgt v1 v2 "icmptmp" gst.builder, TVector (n, TBool))
	      )
	    | TFloat -> ( 
		(build_fcmp Fcmp.Ogt v1 v2 "fcmptmp" gst.builder, TBool)
	      )
	    | TVector (n, TFloat) -> (
		(build_fcmp Fcmp.Ogt v1 v2 "fcmptmp" gst.builder, TVector (n, TBool))
	      )
	    | _ -> raise (Failure "(3)Not Yet implemented")
      )
    | BLeq (e1, e2) -> (
	let (v1, t1) = compile_expr0 gst e1 in
	let (v2, t2) = compile_expr0 gst e2 in
	  match t1 with
	    | TInteger _ | TPtr _ -> ( 
		(build_icmp Icmp.Sle v1 v2 "icmptmp" gst.builder, TBool)
	      )
	    | TVector (n, TInteger _) -> (
		(build_icmp Icmp.Sle v1 v2 "icmptmp" gst.builder, TVector (n, TBool))
	      )
	    | TFloat -> ( 
		(build_fcmp Fcmp.Ole v1 v2 "fcmptmp" gst.builder, TBool)
	      )
	    | TVector (n, TFloat) -> (
		(build_fcmp Fcmp.Ole v1 v2 "fcmptmp" gst.builder, TVector (n, TBool))
	      )
	    | _ -> raise (Failure "(4)Not Yet implemented")
      )
    | BGeq (e1, e2) -> (
	let (v1, t1) = compile_expr0 gst e1 in
	let (v2, t2) = compile_expr0 gst e2 in
	  match t1 with
	    | TInteger _ | TPtr _ -> ( 
		(build_icmp Icmp.Sge v1 v2 "icmptmp" gst.builder, TBool)
	      )
	    | TVector (n, TInteger _) -> (
		(build_icmp Icmp.Sge v1 v2 "icmptmp" gst.builder, TVector (n, TBool))
	      )
	    | TFloat -> ( 
		(build_fcmp Fcmp.Oge v1 v2 "fcmptmp" gst.builder, TBool)
	      )
	    | TVector (n, TFloat) -> (
		(build_fcmp Fcmp.Oge v1 v2 "fcmptmp" gst.builder, TVector (n, TBool))
	      )
	    | _ -> raise (Failure "(5)Not Yet implemented")
      )
    | BNeg b -> (
	let (v, t) = compile_bexpr0 gst b in
	  (build_not v "negtmp" gst.builder, t)
      )
    | BAnd (b1, b2) -> (
	let (v1, t1) = compile_bexpr0 gst b1 in
	let (v2, t2) = compile_bexpr0 gst b2 in
	  (build_and v1 v2 "andtmp" gst.builder, t1)
      )
;;

let rec compile_cmd0 (gst: compile_state) (c: cmd0)  : (llvalue * llvmtype) =
  match c with
    | Unit -> (undef (void_type gst.ctxt), TUnit)
    | Let (asgns, c) -> (
	printf "Let\n"; flush stdout;
	(* first save the previous values *)

	let dm = vmdomain gst.valueenv in
	let vs = Array.fold_left (fun acc hd ->
				    let n = (fst hd) in
				    if vsin n dm then
				      VarMap.add n (VarMap.find n gst.valueenv) acc
				    else
				      acc
				 ) VarMap.empty asgns in

	(* compute new values *)
	  Array.iteri ( fun i (hd1, hd2) ->
			  gst.valueenv <- VarMap.add hd1 (compile_expr0 gst hd2) gst.valueenv	    
		      ) asgns;
	  
	  (* generate body *)
	  let v = compile_cmd0 gst c in

	    (* remove the def *)
	    gst.valueenv <- Array.fold_left (fun acc (hd1, hd2) ->
					       VarMap.remove hd1 acc
					    ) gst.valueenv asgns;
	    
	    (* restore the previous values *)
	    
	    gst.valueenv <- varmap_union vs gst.valueenv;
	    
	    v

      )
    | Seq (cs, e) -> (
	printf "Seq\n"; flush stdout;
	Array.iteri (fun i hd -> let _ = compile_cmd0 gst hd in ()) cs;
	match e with
	  | None -> (undef (void_type gst.ctxt), TUnit)
	  | Some e ->
	      compile_expr0 gst e
      )
    | Return e -> (
	printf "Return\n"; flush stdout;
	let (v, ty) = compile_expr0 gst e in

	  (match ty with
	     | TUnit -> ignore (build_ret_void comp_st.builder)
	     | _ -> ignore (build_ret v comp_st.builder)
	  );
	
	  let cur_block = insertion_block gst.builder in

	  (* ... of the current function *)
	  let cur_fct = block_parent cur_block in
	    
	  (* build then branch  *)
	  let nextblock = append_block gst.ctxt "returnnext" cur_fct in

	    position_at_end nextblock gst.builder;
	    
	    (undef (void_type gst.ctxt), TUnit)
      )
    | If (b, c) -> (
	printf "If\n"; flush stdout;
	(* compute the condition *)
	let (v1, t1) = compile_bexpr0 gst b in

	(* grab the current block ... *)
	let cur_block = insertion_block gst.builder in

	(* ... of the current function *)
	let cur_fct = block_parent cur_block in
	  
	(* build then branch  *)
	let then_startblock = append_block gst.ctxt "then" cur_fct in

	(* build the continuation of the if *)
	let merge_block = append_block gst.ctxt "ifcont" cur_fct in	  

	  (* we build the conditional jmp *)
	  ignore (build_cond_br v1 then_startblock merge_block gst.builder);

	  (* we point to the then branch *)
	  position_at_end then_startblock gst.builder;
	  
	  (* write the code *)
	  let _ = compile_cmd0 gst c in

	    (* and jump to the continuation *) 
	    ignore (build_br merge_block gst.builder);

	    (* we point the continuation *)
	    position_at_end merge_block gst.builder;
	    
	    (undef (void_type gst.ctxt), TUnit)
	    
      )
    | Ifte (b, c1, c2) -> (
	printf "Ifte\n"; flush stdout;
	let (v1, t1) = compile_bexpr0 gst b in

	(* grab the current block ... *)
	let cur_block = insertion_block gst.builder in

	(* ... of the current function *)
	let cur_fct = block_parent cur_block in
	  
	(* build then branch  *)
	let then_startblock = append_block gst.ctxt "then" cur_fct in

	(* build the else branch  *)
	let else_startblock = append_block gst.ctxt "else" cur_fct in

	(* build the continuation of the if *)
	let merge_block = append_block gst.ctxt "iftecont" cur_fct in	  

	  (* we build the conditional jmp *)
	  ignore (build_cond_br v1 then_startblock else_startblock gst.builder);

	  (* compile then branch *)
	  position_at_end then_startblock gst.builder;
	  let (vthen, tythen) = compile_cmd0 gst c1 in
	  ignore (build_br merge_block gst.builder);	    
	    

	  (* grab the current block ... *)
	  let then_lastblock = insertion_block gst.builder in
	    
	  (* compile else branch *)
	  position_at_end else_startblock gst.builder;
	  let (velse, tyelse) = compile_cmd0 gst c2 in
	  ignore (build_br merge_block gst.builder);	    

	  (* grab the current block ... *)
	  let else_lastblock = insertion_block gst.builder in

	    (* build merge *)
	    position_at_end merge_block gst.builder;
	    let v = build_phi [(vthen, then_lastblock); (velse, else_lastblock)] "ifte_merge" gst.builder in
	      (v, t1)
	    

      )
    | While (b, c) -> (
	printf "While\n"; flush stdout;
	(* grab the current block ... *)
	let cur_block = insertion_block gst.builder in

	(* ... of the current function *)
	let cur_fct = block_parent cur_block in
	  
	(* build the cond block  *)
	let cond_block = append_block gst.ctxt "cond" cur_fct in

	(* build the next branch  *)
	let next_block = append_block gst.ctxt "next" cur_fct in

	(* build the body branch  *)
	let body_block = append_block gst.ctxt "body" cur_fct in
	  
	  (* jump to cond block *)
	  ignore (build_br cond_block gst.builder);	    
	  
	  (* Condition block *)
	  position_at_end cond_block gst.builder;
	  let (v, ty) = compile_bexpr0 gst b in
	    ignore (build_cond_br v body_block next_block gst.builder);

	    (* body block *)
	    position_at_end body_block gst.builder;
	    ignore (compile_cmd0 gst c);
	    ignore (build_br cond_block gst.builder);
	    
	    (* next block *)
	    position_at_end next_block gst.builder;
	    
	    (undef (void_type gst.ctxt), TUnit)	  
	
      )
    | Switch (e, c, d) -> (
	printf "Switch\n"; flush stdout;
	(* grab the current block ... *)
	let switch_block = insertion_block gst.builder in

	(* ... of the current function *)
	let cur_fct = block_parent switch_block in

	(* build the merge *)
	let merge_block = append_block gst.ctxt "merge" cur_fct in

	(* build default branch  *)
	let default_startblock = append_block gst.ctxt "default" cur_fct in

	  position_at_end default_startblock gst.builder;
	  let (default_v, default_ty) = compile_cmd0 gst d in
	    
	    ignore (build_br merge_block gst.builder);	    

	    (* grab the current block ... *)
	    let default_lastblock = insertion_block gst.builder in
	    
	      (* build the initial phi *)
	      position_at_end merge_block gst.builder;
	      let mphi = build_phi [(default_v, default_lastblock)] "switchmerge" gst.builder in

		(* build the switch *)
		position_at_end switch_block gst.builder;
		let (vcond, tycond) = compile_expr0 gst e in
		let switch = build_switch vcond default_startblock (Array.length c) gst.builder in
		  
		  Array.iteri (fun i (v, c) -> 
				 let case_startblock = append_block gst.ctxt "case" cur_fct in
				   position_at_end case_startblock gst.builder;
				   let (case_v, case_ty) = compile_cmd0 gst d in				     
				   let case_lastblock = insertion_block gst.builder in
				     ignore (build_br merge_block gst.builder);	
				     let (casev, casety) = compute_cste gst v in
				       add_case switch casev case_startblock;
				       add_incoming (case_v, case_lastblock) mphi				   
			      ) c;
		  (mphi, default_ty)

      )
    | Value e -> (
	printf "Value\n";  flush stdout;
	compile_expr0 gst e
      )
    | Assign (lval, e) -> (
	printf "Assign\n";  flush stdout;
	let (e_v, e_ty) = compile_expr0 gst e in
	  match lval with
	    | LVar s -> (
		let (var_v, var_ty) = VarMap.find s gst.valueenv in
		  ignore (build_store e_v var_v gst.builder);
		  (undef (void_type gst.ctxt), TUnit)	  
	      )
	    | LNth (s, i) -> (
		
		let (iv, it) = compile_expr0 gst i in
		let (sv, st) = compile_expr0 gst s in
		let zero = const_int (integer_type gst.ctxt 32) 0 in
		let one = const_int (integer_type gst.ctxt 32) 1 in
		  match st with
		    | TPtr (TArray (i, ty)) -> (
			
			let ptr = build_gep sv [| zero; one; iv |] "arraystore" gst.builder in
			  ignore (build_store e_v ptr gst.builder);
			  (undef (void_type gst.ctxt), TUnit)	  
			    
		      )
		    | TPtr (TTuple tys) -> (

			  match i with
			    | ECste (CInt (n, i)) ->
				let ptr = build_struct_gep sv i "tuplelookup" gst.builder in
				  ignore (build_store e_v ptr  gst.builder);
				    (undef (void_type gst.ctxt), TUnit)	  				  
			    | _ -> raise (Failure "tuple lookup only for constante")
				
		      )
		    | TVector (i, ty) -> (
			
			(build_insertelement sv e_v iv "vector insert" gst.builder, ty)
			  
		      )
		    | TPtr ty -> (
			let ptr = build_gep sv [| iv |] "arraystore" gst.builder in
			  ignore (build_store e_v ptr gst.builder);
			  (undef (void_type gst.ctxt), TUnit)	  			
		      )
	      )
      )
;;


let rec compile_block0 (gst: compile_state) (b: block0)  : (llvalue * llvmtype) =
  match b with
    | Expr (s, c, retty) -> (
	let fty = (build_llvmtype gst VarMap.empty (TFct ([| |], retty))) in
	let f = declare_function s fty gst.modul in
	let entryb = append_block gst.ctxt "entry" f in
	  position_at_end entryb gst.builder;
	  let (v, ty) = compile_cmd0 gst c in
	    (match ty with
	       | TUnit -> ignore (build_ret_void gst.builder)
	       | _ -> ignore (build_ret v gst.builder)
	    );
	    Llvm_analysis.assert_valid_function f;
	    if gst.optimize then ignore(PassManager.run_function f gst.passmng);
	    gst.valueenv <- VarMap.add s (f, TPtr (TFct ([| |], retty))) gst.valueenv;
	    (f, TPtr (TFct ([| |], retty)))
      )
    | Fct (name, args, retty, body) -> (
	let fty = TFct (Array.map fst args, retty) in
	let llvmfty = (build_llvmtype gst VarMap.empty fty) in
	let f = declare_function name llvmfty gst.modul in
	let entryb = append_block gst.ctxt "entry" f in
	  position_at_end entryb gst.builder;
	  
	  (* save the previous values *)
	  let dm = vmdomain gst.valueenv in
	  let vs = Array.fold_left (fun acc hd ->
				      let n = (snd hd) in
					if vsin n dm then
					  VarMap.add n (VarMap.find n gst.valueenv) acc
					else
					  acc
				   ) VarMap.empty args in
	    
	    (* set new values *)
	    Array.iteri ( fun i hd ->
			    set_value_name (snd args.(i)) hd;
			    gst.valueenv <- VarMap.add (snd args.(i)) (hd, fst args.(i)) gst.valueenv	    
			) (params f);

	    (* generate body *)
	    let (v, ty) = compile_cmd0 gst body in
	      (match ty with
		 | TUnit -> ignore (build_ret_void gst.builder)
		 | _ -> ignore (build_ret v gst.builder)
	      );
	      
	      
	      (* remove the def *)
	      gst.valueenv <- Array.fold_left (fun acc (hd1, hd2) ->
						 VarMap.remove hd2 acc
					      ) gst.valueenv args;
	      
	      (* restore the previous values *)
	      
	      gst.valueenv <- varmap_union vs gst.valueenv;

	      Llvm_analysis.assert_valid_function f;
	      if gst.optimize then ignore(PassManager.run_function f gst.passmng);
	      gst.valueenv <- VarMap.add name (f, TPtr fty) gst.valueenv;
	      (f, TPtr fty)
	
      )
    | Extern (name, args, retty) -> (
	let fty = TFct (Array.map fst args, retty) in
	let llvmfty = (build_llvmtype gst VarMap.empty fty) in
	let f = declare_function name llvmfty gst.modul in
	
	  Array.iteri ( fun i hd ->
			  set_value_name (snd args.(i)) hd;
		      ) (params f);
	  gst.valueenv <- VarMap.add name (f, TPtr fty) gst.valueenv;
	  (f, TPtr fty)

      )
    | GCste (name, c) -> (
	let (v, ty) = compute_cste gst c in
	  gst.valueenv <- VarMap.add name (v, ty) gst.valueenv;
	  (v, ty)
      )
    | Global (name, c) -> (
	let (v, ty) = compute_cste gst c in
	let g = define_global name v gst.modul in
	  gst.valueenv <- VarMap.add name (g, TPtr ty) gst.valueenv;
	  (g, TPtr ty)

      )
;;

(**************************************************************)
