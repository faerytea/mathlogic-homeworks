all : homework1 homework2 homework3

homework1 : Mathlogic.o Mathlogic/Annotations.o homework1.hs
	ghc -O2 homework1

homework2 : Mathlogic.o Mathlogic/Deduction.o homework2.hs
	ghc -O2 homework2

homework3 : Mathlogic.o Mathlogic/Proof.o homework3.hs
	ghc -O2 homework3

Mathlogic/Annotations.o : Mathlogic.o Mathlogic/Parser.o Mathlogic/Annotations.hs
	ghc -O2 Mathlogic/Annotations.hs

Mathlogic/Deduction.o : Mathlogic.o Mathlogic/Parser.o Mathlogic/Deduction.hs
	ghc -O2 Mathlogic/Deduction.hs

Mathlogic/Proof.o : Mathlogic.o Mathlogic/Parser.o Mathlogic/Deduction.o Mathlogic/Proof.hs
	ghc -O2 Mathlogic/Proof.hs

Mathlogic.o : Mathlogic/Parser.o Mathlogic/Tokens.o Mathlogic/Axioms.o Mathlogic.hs
	ghc -O2 Mathlogic.hs

Mathlogic/Axioms.o : Mathlogic/Parser.o Mathlogic/Tokens.o Mathlogic/Axioms.hs
	ghc -O2 Mathlogic/Axioms.hs

Mathlogic/Parser.o : Mathlogic/Tokens.o Mathlogic/Parser.y
	happy Mathlogic/Parser.y
	ghc -O2 Mathlogic/Parser.hs

Mathlogic/Tokens.o : Mathlogic/Tokens.x
	alex Mathlogic/Tokens.x
	ghc -O2 Mathlogic/Tokens.hs

Mathlogic/Predicates/Parser.o : Mathlogic/Predicates/Tokens.o Mathlogic/Predicates/Parser.y
	happy Mathlogic/Predicates/Parser.y
	ghc -O2 Mathlogic/Predicates/Parser.hs

Mathlogic/Predicates/Tokens.o : Mathlogic/Predicates/Tokens.x
	alex Mathlogic/Predicates/Tokens.x
	ghc -O2 Mathlogic/Predicates/Tokens.hs

clean :
	rm -f ./Mathlogic/*.hi ./Mathlogic/*.o ./Mathlogic/*.exe                                        # files in Mathlogic dir
	rm -f ./Mathlogic/Predicates/*.hi ./Mathlogic/Predicates/*.o ./Mathlogic/Predicates/*.exe       # files in Mathlogic/Predicates dir
	rm -f homework1 homework2 homework3 *.hi *.o *.exe                                              # files in root dir
	rm -f Mathlogic/Parser.hs Mathlogic/Tokens.hs Mathlogic/*.info                                  # some generated files in Mathlogic dir
	rm -f Mathlogic/Predicates/Parser.hs Mathlogic/Predicates/Tokens.hs Mathlogic/Predicates/*.info # some generated files in Mathlogic/Predicates dir
