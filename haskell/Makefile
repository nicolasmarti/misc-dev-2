ghc := ghc
ghcflags := 
# -DHAS_GETPOINTERTOGLOBAL=1
packages := -ignore-package monads-fd
examples := Test Trep

all: $(examples:%=%.exe)

%.exe: %.hs
	$(ghc) $(ghcflags) --make $(packages) -o $(basename $<).exe -main-is $(basename $<).main $<

%.run: %.exe
	./$<

#%.exe: %.bc
#	llvm-ld -native -disable-opt -o $(basename $<).exe $<

%.exe: %.s
	gcc -o $(basename $<).exe $<

%.s: %.bc
	llc -filetype=asm $<

run:	$(examples:%=%.run)

clean:
	rm -f $(examples) *.vmo *.vm *.o *.hi *.s *.bc *.ll *.exe *.exe.manifest *~ *stub.*
