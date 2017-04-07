{
module Mathlogic.Parser where
import Mathlogic.Tokens
import Data.List(intercalate)
}

%name happilyParseExpression Expr
%name happilyParseFile12 F12
%name happilyParseProofList ProofList
%tokentype { Symbol }
%error { error {- . (++) "Cannot parse: " . concat . map -} . show }

%token
    '->'                      { Impl }
    '|'                       { Disj }
    '&'                       { Conj }
    '('                       { LB }
    ')'                       { RB }
    '!'                       { No }
    ','                       { Comma }
    '|-'                      { EOP }
    'n'                       { NL }
    'v'                       { PV $$ }

%nonassoc '|-'
%right '->'
%left '|'
%left '&'

%%

F12
    : Head 'n' Prf            { File12 $1 $3 }
    | Head 'n'                { File12 $1 (Proof []) }
    
Head
    : '|-' Expr               { Hdr [] $2 }
    | ExpList '|-' Expr       { Hdr (reverse $1) $3 }

ExpList
    : Expr                    { $1 : [] }
    | ExpList ',' Expr        { $3 : $1 }

Prf : ProofList 'n'           { Proof (reverse $1) }

ProofList
    : Expr                    { $1 : [] }
    | ProofList 'n' Expr      { $3 : $1 }
    
Expr
    : Disjunct                { Ae $1 }
    | Disjunct '->' Expr      { Implication $1 $3 }

Disjunct
    : Conjunct                { Ad $1 }
    | Disjunct '|' Conjunct   { Or $1 $3 }
    
Conjunct
    : Tok                     { Ac $1 }
    | Conjunct '&' Tok        { And $1 $3 }

Tok
    : 'v'                     { Token (PVar $1) }
    | '!' Tok                 { Not $2 }
    | '(' Expr ')'            { An $2 }

{
data FakeMT = FakeT Token
            | FakeD Disjunction
            | FakeC Conjunction
            | FakeE Expression

class MathlogicToken a where
    decompose      :: a -> a
    collectMT      :: (String -> s -> s) -> s -> a -> s
    fakeWrap       :: a -> FakeMT
    unwrap         :: FakeMT -> a
    makeExpression :: a -> Expression
    -- экзистенциальные типы (на самом деле тут костыль-обёртка)

mapMT :: (MathlogicToken a, MathlogicToken b, MathlogicToken c) => (a -> s -> s) -> (b -> s -> s -> s) -> (String -> s) -> c -> s
mapMT exit1 exit2 transform exp = mapFMT (wrapfn exit1) (wrapfn exit2) transform (fakeWrap exp) where
    wrapfn f = \x -> f (unwrap x)
    
    -- The BIGGEST crutch in this project
mapFMT :: (FakeMT -> s -> s) -> (FakeMT -> s -> s -> s) -> (String -> s) -> FakeMT -> s
mapFMT exit1 exit2 transform exp@(FakeE (Implication d e)) = exit2 exp (mapFMT exit1 exit2 transform (fakeWrap d)) (mapFMT exit1 exit2 transform (fakeWrap e))
mapFMT exit1 exit2 transform exp@(FakeE (Ae a))            = exit1 exp (mapFMT exit1 exit2 transform (fakeWrap a))
mapFMT exit1 exit2 transform exp@(FakeD (Or d e))          = exit2 exp (mapFMT exit1 exit2 transform (fakeWrap d)) (mapFMT exit1 exit2 transform (fakeWrap e))
mapFMT exit1 exit2 transform exp@(FakeD (Ad a))            = exit1 exp (mapFMT exit1 exit2 transform (fakeWrap a))
mapFMT exit1 exit2 transform exp@(FakeC (And d e))         = exit2 exp (mapFMT exit1 exit2 transform (fakeWrap d)) (mapFMT exit1 exit2 transform (fakeWrap e))
mapFMT exit1 exit2 transform exp@(FakeC (Ac a))            = exit1 exp (mapFMT exit1 exit2 transform (fakeWrap a))
mapFMT exit1 exit2 transform exp@(FakeT (Not d))           = exit1 exp (mapFMT exit1 exit2 transform (fakeWrap d))
mapFMT exit1 exit2 transform exp@(FakeT (An a))            = exit1 exp (mapFMT exit1 exit2 transform (fakeWrap a))
mapFMT exit1 exit2 transform (FakeT (Scheme a))            = transform [a]
mapFMT exit1 exit2 transform (FakeT (Token (PVar a)))      = transform a

getProofFromFile12 (File12 _ (Proof proof)) = proof

data PropVariable = PVar String
data Token = Token PropVariable | Not Token | An Expression | Scheme Char 
data Conjunction = Ac Token | And Conjunction Token 
data Disjunction = Ad Conjunction | Or Disjunction Conjunction 
data Expression = Ae Disjunction | Implication Disjunction Expression 

data Header = Hdr [Expression] Expression
data Proof = Proof [Expression]
data File12 = File12 Header Proof

instance Show PropVariable where
    show (PVar a) = a

instance Show Token where
    show (Token  a) = show a
    show (Not    a) = '!':(show a)
    show (An     a) = '(':(show a ++ ")")
    show (Scheme a) = '~':[a]

instance Show Conjunction where
    show (Ac  a)   = show a
    show (And a b) = (show a) ++ ('&':(show b))

instance Show Disjunction where
    show (Ad a)   = show a
    show (Or a b) = (show a) ++ ('|':(show b))

instance Show Expression where
    show (Ae          a)   = show a
    show (Implication a b) = (show a) ++ ("->" ++ (show b))

instance Show Header where
    show (Hdr pre exp) = (intercalate "," (map show pre)) ++ "|-" ++ (show exp)

instance Show File12 where
    show (File12 hdr (Proof list)) = (show hdr) ++ ('\n':(intercalate "\n" (map show list)))

instance Eq PropVariable where
    (==) (PVar a) (PVar b) = a == b

instance Eq Token where
    (==) (Token a) (Token b) = a == b
    (==) (Not   a) (Not   b) = a == b
    (==) (An    a) (An    b) = a == b
    (==) _         _         = False

instance Eq Conjunction where
    (==) (Ac  a)   (Ac  b)   = a == b
    (==) (And a b) (And c d) = (a == c) && (b == d)
    (==) _         _         = False

instance Eq Disjunction where
    (==) (Ad a)   (Ad b)   = a == b
    (==) (Or a b) (Or c d) = (a == c) && (b == d)
    (==) _        _        = False

instance Eq Expression where
    (==) (Ae          a)   (Ae          b)   = a == b
    (==) (Implication a b) (Implication c d) = (a == c) && (b == d)
    (==) _                 _                 = False

instance MathlogicToken Expression where
    decompose (Ae (Ad (Ac (An a)))) = decompose a
    decompose (Implication d e)     = Implication (decompose d) (decompose e)
    decompose (Ae a)                = Ae (decompose a)
    collectMT f state (Implication d e) = collectMT f (collectMT f state d) e
    collectMT f state (Ae a)            = collectMT f state a
    fakeWrap a = FakeE a
    unwrap (FakeE a) = a
    makeExpression e = decompose e

instance MathlogicToken Disjunction where
    decompose (Ad (Ac (An (Ae a)))) = decompose a
    decompose (Or d c)              = Or (decompose d) (decompose c)
    decompose (Ad a)                = Ad (decompose a)
    collectMT f state (Or d e)          = collectMT f (collectMT f state d) e
    collectMT f state (Ad a)            = collectMT f state a
    fakeWrap a = FakeD a
    unwrap (FakeD a) = a
    makeExpression d = decompose $ Ae d

instance MathlogicToken Conjunction where
    decompose (Ac (An (Ae (Ad a)))) = decompose a
    decompose (And c t)             = And (decompose c) (decompose t)
    decompose (Ac a)                = Ac (decompose a)
    collectMT f state (And d e)         = collectMT f (collectMT f state d) e
    collectMT f state (Ac a)            = collectMT f state a
    fakeWrap a = FakeC a
    unwrap (FakeC a) = a
    makeExpression c = decompose $ Ae $ Ad c

instance MathlogicToken Token where
    decompose (An (Ae (Ad (Ac a)))) = decompose a
    decompose (Not t)               = Not (decompose t)
    decompose (An a)                = An (decompose a)
    decompose  a                    = a
    collectMT f state (Token (PVar a))  = f  a  state
    collectMT f state (Scheme a)        = f [a] state
    collectMT f state (Not a)           = collectMT f state a
    collectMT f state (An a)            = collectMT f state a
    fakeWrap a = FakeT a
    unwrap (FakeT a) = a
    makeExpression t = decompose $ Ae $ Ad $ Ac t
}
