all : homework1 homework2 homework3

homework1 : Mathlogic.o Mathlogic/Annotations.o
	ghc -O2 homework1

homework2 : Mathlogic.o Mathlogic/Deduction.o
	ghc -O2 homework2

homework3 : Mathlogic.o Mathlogic/Proof.o
	ghc -O2 homework3

Mathlogic/Annotations.o : Mathlogic.o Mathlogic/Parser.o
	ghc -O2 Mathlogic/Annotations.hs

Mathlogic/Deduction.o : Mathlogic.o Mathlogic/Parser.o
	ghc -O2 Mathlogic/Deduction.hs

Mathlogic/Proof.o : Mathlogic.o Mathlogic/Parser.o Mathlogic/Deduction.o
	ghc -O2 Mathlogic/Proof

Mathlogic.o : Mathlogic/Parser.o Mathlogic/Tokens.o Mathlogic/Axioms.o
	ghc -O2 Mathlogic.hs

Mathlogic/Axioms.o : Mathlogic/Parser.o Mathlogic/Tokens.o
	ghc -O2 Mathlogic/Axioms.hs

Mathlogic/Parser.o : Mathlogic/Tokens.o
	happy Mathlogic/Parser.y
	ghc -O2 Mathlogic/Parser.hs

Mathlogic/Tokens.o : 
	alex Mathlogic/Tokens.x
	ghc -O2 Mathlogic/Tokens.hs

clean :
	rm -f ./Mathlogic/*.hi ./Mathlogic/*.o ./Mathlogic/*.exe *.hi *.o *.exe homework1 homework2 homework3 Mathlogic/Parser.hs Mathlogic/Tokens.hs
