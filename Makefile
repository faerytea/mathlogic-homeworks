all : homework1 homework2

homework1 : MathlogicCommon.o
	ghc -O2 homework1

homework2 : MathlogicCommon.o
	ghc -O2 homework2

MathlogicCommon.o : MathlogicParser.hs
	ghc -O2 MathlogicCommon.hs

MathlogicParser.hs : MathlogicTokens.hs
	happy MathlogicParser.y

MathlogicTokens.hs : 
	alex MathlogicTokens.x

clean :
	rm -f *.hi *.o *.exe homework1 homework2 MathlogicParser.hs MathlogicTokens.hs
