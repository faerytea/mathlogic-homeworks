{
module MathlogicParser where
import MathlogicTokens
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
class MathlogicToken a where
    decompose :: a -> a
    collectMT :: (String -> s -> s) -> s -> a -> s
    -- mapMT :: MathlogicToken b => (a -> s -> s) -> (a -> s -> s -> s) -> (String -> s) -> s -> b -> s

data PropVariable = PVar String --deriving (MathlogicToken)
data Token = Token PropVariable | Not Token | An Expression | Scheme Char --deriving (MathlogicToken)
data Conjunction = Ac Token | And Conjunction Token --deriving (MathlogicToken)
data Disjunction = Ad Conjunction | Or Disjunction Conjunction --deriving (MathlogicToken)
data Expression = Ae Disjunction | Implication Disjunction Expression --deriving (MathlogicToken)

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
    -- mapMT exit1 exit2 transform state exp@(Implication d e) = exit2 exp (mapMT exit1 exit2 transform state d) (mapMT exit1 exit2 transform state e)
    -- mapMT exit1 exit2 transform state exp@(Ae a)            = exit1 exp (mapMT exit1 exit2 transform state a)

instance MathlogicToken Disjunction where
    decompose (Ad (Ac (An (Ae a)))) = decompose a
    decompose (Or d c)              = Or (decompose d) (decompose c)
    decompose (Ad a)                = Ad (decompose a)
    collectMT f state (Or d e)          = collectMT f (collectMT f state d) e
    collectMT f state (Ad a)            = collectMT f state a
    -- mapMT exit1 exit2 transform state exp@(Or d e)          = exit2 exp (mapMT exit1 exit2 transform state d) (mapMT exit1 exit2 transform state e)
    -- mapMT exit1 exit2 transform state exp@(Ad a)            = exit1 exp (mapMT exit1 exit2 transform state a)

instance MathlogicToken Conjunction where
    decompose (Ac (An (Ae (Ad a)))) = decompose a
    decompose (And c t)             = And (decompose c) (decompose t)
    decompose (Ac a)                = Ac (decompose a)
    collectMT f state (And d e)         = collectMT f (collectMT f state d) e
    collectMT f state (Ac a)            = collectMT f state a
    -- mapMT exit1 exit2 transform state exp@(And d e)         = exit2 exp (mapMT exit1 exit2 transform state d) (mapMT exit1 exit2 transform state e)
    -- mapMT exit1 exit2 transform state exp@(Ac a)            = exit1 exp (mapMT exit1 exit2 transform state a)

instance MathlogicToken Token where
    decompose (An (Ae (Ad (Ac a)))) = decompose a
    decompose (Not t)               = Not (decompose t)
    decompose (An a)                = An (decompose a)
    decompose  a                    = a
    collectMT f state (Token (PVar a))  = f  a  state
    collectMT f state (Scheme a)        = f [a] state
    collectMT f state (Not a)           = collectMT f state a
    collectMT f state (An a)            = collectMT f state a
    -- mapMT exit1 exit2 transform state exp@(Not d)           = exit1 exp (mapMT exit1 exit2 transform state d)
    -- mapMT exit1 exit2 transform state exp@(An a)            = exit1 exp (mapMT exit1 exit2 transform state a)
    -- mapMT exit1 exit2 transform state (Scheme a)            = transform [a]
    -- mapMT exit1 exit2 transform state (Token (PVar a))      = transform a
}
