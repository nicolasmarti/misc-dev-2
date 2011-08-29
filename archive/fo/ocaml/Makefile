CC=ocamlopt #-p
PROG=fo

main: parser
	$(CC) -o $(PROG) varset.cmx def.cmx pprinter.cmx trans.cmx solve.cmx lexer.cmx grammar.cmx main.cmx

parser: def.ml trans.ml pprinter.ml lexer.mll grammar.mly main.ml
	$(CC) -c varset.ml
	$(CC) -c def.ml
	$(CC) -c pprinter.ml
	$(CC) -c trans.ml
	$(CC) -c solve.ml
	ocamlyacc grammar.mly
	ocamllex lexer.mll
	$(CC) -c grammar.mli
	$(CC) -c lexer.ml
	$(CC) -c grammar.ml
	$(CC) -c main.ml 

clean:
	rm -f *.cmo *.cmi *.cmx *.o lexer.ml grammar.ml grammar.mli $(PROG)

