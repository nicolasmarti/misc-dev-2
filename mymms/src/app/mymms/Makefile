#This file is part of Mymms.

#Mymms is free software: you can redistribute it and/or modify
#it under the terms of the GNU General Public License as published by
#the Free Software Foundation, either version 3 of the License, or
#(at your option) any later version.

#Mymms is distributed in the hope that it will be useful,
#but WITHOUT ANY WARRANTY; without even the implied warranty of
#MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#GNU General Public License for more details.

#You should have received a copy of the GNU General Public License
#along with Mymms.  If not, see <http://www.gnu.org/licenses/>.

# Copyright (C) 2008 Nicolas Marti

NATURE = executable

FILES = mymms.$(EXT)


INCLUDE = ./ -I ../../lib/ \
	-I ../../core/kernel/ \
	-I ../../core/proof/ \
	-I ../../core/minima/ \
	-I ../primitives/ \
	-I ../../oracles/ \
	-I ../parser \
	-I ../python/

ifeq ($(LLVM),1)
LLVMLIB = llvm.cmxa \
	llvm_executionengine.cmxa \
	llvm_target.cmxa \
	llvm_scalar_opts.cmxa \
	llvm_analysis.cmxa \
	llvm_bitreader.cmxa \
	llvm_bitwriter.cmxa \
	../../core/jit/jit.cmxa

else
LLVMLIB =
endif

ifeq ($(PYTHON),1)
PYTHONLIB = /usr/lib/ocaml/pycaml/pycaml.cmxa \
	../python/python.cmxa 

else
PYTHONLIB =
endif

CCOPT = -pp cpp


LIBRARY = ../../lib/lib.cmxa \
	../../core/kernel/kernel.cmxa \
	../../core/interp/interp.cmxa \
	../../core/vm/vm.cmxa \
	../../core/proof/proof.cmxa \
	dynlink.cmxa \
	$(LLVMLIB) \
	../../core/minima/minima.cmxa \
	nums.cmxa \
	bigarray.cmxa \
	../primitives/primitives.cmxa \
	../../oracles/oracles.cmxa \
	../parser/parser.cmxa \
	$(PYTHONLIB) 	

OPTION = -cc g++ -ccopt -L/usr/lib/ocaml/gsl -ccopt -L/usr/lib/ocaml/pycaml


EXEC = mymms

include ../../../Makefile.inc
