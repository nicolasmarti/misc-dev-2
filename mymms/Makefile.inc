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


CC = ocamlopt #-p 
#CC = ocamlcp -p a
EXT = cmx
#EXT = cmo
LIBEXT = cmxa
#CCOPT =

# the files to build
#FILES = 

# the directory to include
#INCLUDE = 

# the library to include 
#LIBRARY = 

# the name of the library to build
#LIB = 

# the name of the executable to build
#EXEC = 

# the recurrent repository to consider
#REP = 

#PLUGIN

# The nature of the build
# NATURE = executable | library | repository | objects | plugin

all: $(NATURE)

executable: $(FILES)
	$(CC) -o $(EXEC) $(LIBRARY) $(OPTION) $(^) 

library: $(FILES)
	$(CC) -a -o $(LIB) $(LIBRARY) $(^) 

repository:
	@for i in $(REP); do make -C $$i all; done

objects: $(FILES)


plugin: $(FILES)
	$(CC) -shared -o $(PLUGIN) $(LIBRARY) $(^) 

clean:
	@rm -f *.mo *.cmxa *.cmo *.mli *.cmi *.cmx *.cmxs *.o *.out *.dump lexer_*.ml parser_*.ml parser_*.mli *.a $(EXEC) *.exe *~ && for i in $(REP); do make -C $$i clean; done	

%.cmx: %.ml
	$(CC) -I $(INCLUDE) $(CCOPT) -c $(<)

%.cmo: %.ml %.cmi
	$(CC) -I $(INCLUDE) $(CCOPT) -c $(<)

%.cmi: %.ml 
	$(CC) -I $(INCLUDE) $(CCOPT) -c $(<)

%.ml: %.mll $(KERNELFILES)
	ocamllex $(<)

%.ml: %.mli $(KERNELFILES)
	$(CC)  -I $(INCLUDE) -c $(<)

%.mli: %.mly $(KERNELFILES)
	ocamlyacc $(<)

%.mo: %.m
	mymms -o $(<)