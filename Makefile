all : homework1 homework2 homework3 homework4 homework5

homework1 : Mathlogic.o Mathlogic/Annotations.o homework1.hs
	ghc -O2 homework1

homework2 : Mathlogic.o Mathlogic/Deduction.o homework2.hs
	ghc -O2 homework2

homework3 : Mathlogic.o Mathlogic/Proof.o homework3.hs
	ghc -O2 homework3

homework4 : Mathlogic/Predicates/Deduction.o Mathlogic/Predicates/Parser.o homework4.hs
	ghc -O2 homework4

homework5 : Mathlogic/Predicates/Parser.o Mathlogic/Predicates/Sum.o homework5.hs
	ghc -O2 homework5

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

Mathlogic/Predicates/Checker.o : Mathlogic/Predicates/Parser.o Mathlogic/Predicates/Axioms.o
	ghc -O2 Mathlogic/Predicates/Checker.hs

Mathlogic/Predicates/Axioms.o : Mathlogic/Predicates/Parser.o Mathlogic/Predicates/Tokens.o Mathlogic/Predicates/Axioms.hs
	ghc -O2 Mathlogic/Predicates/Axioms.hs

Mathlogic/Predicates/Parser.o : Mathlogic/Predicates/Tokens.o Mathlogic/Predicates/Parser.y
	happy Mathlogic/Predicates/Parser.y
	ghc -O2 Mathlogic/Predicates/Parser.hs

Mathlogic/Predicates/Tokens.o : Mathlogic/Predicates/Tokens.x
	alex Mathlogic/Predicates/Tokens.x
	ghc -O2 Mathlogic/Predicates/Tokens.hs

Mathlogic/Predicates/Deduction.o : Mathlogic/Predicates/Deduction.hs Mathlogic/Predicates/Checker.o Mathlogic/Predicates/Parser.o
	ghc -O2 Mathlogic/Predicates/Deduction.hs

Mathlogic/Predicates/Sum.o : Mathlogic/Predicates/Parser.o Mathlogic/Predicates/Sum.hs
	ghc -O2 Mathlogic/Predicates/Sum.hs

test4A : test4iA test4cA

test4iA : test4i1 test4i2 test4i3 test4i4 test4i5 test4i6 test4i7 test4i8 test4i9 test4i10 test4i11

test4cA : test4c1 test4c2 test4c5 test4c6 test4c7 test4c8 test4c9 test4c10 test4c11 test4c11 test4c11 test4c14 test4c15

Mathlogic/Predicates/Main : Mathlogic/Predicates/Main.hs Mathlogic/Predicates/Checker.o Mathlogic/Predicates/Parser.o
	ghc -O2 Mathlogic/Predicates/Main.hs

test4c% : ../logic2014/tests/HW4/correct%.in Mathlogic/Predicates/Main
	Mathlogic/Predicates/Main $<

test4i% : ../logic2014/tests/HW4/incorrect%.in Mathlogic/Predicates/Main
	Mathlogic/Predicates/Main $<

clean :
	rm -f ./Mathlogic/*.hi ./Mathlogic/*.o ./Mathlogic/*.exe                                        # files in Mathlogic dir
	rm -f ./Mathlogic/Predicates/*.hi ./Mathlogic/Predicates/*.o ./Mathlogic/Predicates/*.exe       # files in Mathlogic/Predicates dir
	rm -f homework1 homework2 homework3 homework4 homework5 *.hi *.o *.exe                          # files in root dir
	rm -f Mathlogic/Parser.hs Mathlogic/Tokens.hs Mathlogic/*.info                                  # some generated files in Mathlogic dir
	rm -f Mathlogic/Predicates/Parser.hs Mathlogic/Predicates/Tokens.hs Mathlogic/Predicates/*.info # some generated files in Mathlogic/Predicates dir
