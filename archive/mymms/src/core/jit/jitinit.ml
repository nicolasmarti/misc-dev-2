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

open Llvm;;
open Llvm_executionengine;;
open Llvm_target;;
open Llvm_scalar_opts;;

open Def;;


exception Error of string

let ctxt = (create_context ())
let the_module = create_module ctxt "mymms jit"
let builder = builder ctxt
let named_values:(string, (llvalue * term)) Hashtbl.t = Hashtbl.create 10

(* Create the JIT. *)
let the_module_provider = ModuleProvider.create the_module
;;

let the_execution_engine = ExecutionEngine.create the_module_provider
;;

let the_fpm = PassManager.create_function the_module_provider
;;

let jit_init () =

  (* Set up the optimizer pipeline.  Start with registering info about how the
   * target lays out data structures. *)
  TargetData.add (ExecutionEngine.target_data the_execution_engine) the_fpm;
  
  (* Do simple "peephole" optimizations and bit-twiddling optzn. *)
  add_instruction_combining the_fpm;
  
  (* reassociate expressions. *)
  add_reassociation the_fpm;
  
  (* Eliminate Common SubExpressions. *)
  add_gvn the_fpm;
  
  (* Simplify the control flow graph (deleting unreachable blocks, etc). *)
  add_cfg_simplification the_fpm
;;
