{
module Mathlogic.Predicates.Parser where
import Mathlogic.Predicates.Tokens
import Data.List(intercalate)
import qualified Data.Set as DS
}

%name happilyParseExpression Expr
%name happilyParseFile4 F4
%name happilyParseProofList ProofList
%tokentype { Symbol }
%error { error {- . (++) "Cannot parse: " . concat . map -} . show }

%token
    '~'                       { Magic }
    '->'                      { Impl }
    '|'                       { Disj }
    '&'                       { Conj }
    '('                       { LB }
    ')'                       { RB }
    '!'                       { No }
    '@'                       { ForAll }
    '?'                       { Exists }
    '='                       { Equals }
    '+'                       { Add }
    '*'                       { Multiply }
    '\''                      { Hatch' }
    '0'                       { Zero' }
    ','                       { Comma }
    '|-'                      { EOP }
    'n'                       { NL }
    'v'                       { Fun $$ }
    'p'                       { Pred $$ }

%nonassoc '|-'
%right '->'
%left '|'
%left '&'
%left '+'
%left '*'

%%

F4
    : Head 'n' Prf            { File4 $1 $3 }
    | Head 'n'                { File4 $1 [] }
    
Head
    : '|-' Expr               { Hdr [] $2 }
    | ExpList '|-' Expr       { Hdr (reverse $1) $3 }

ExpList
    : Expr                    { $1 : [] }
    | ExpList ',' Expr        { $3 : $1 }

Prf : ProofList 'n'           { reverse $1 }

ProofList
    : Expr                    { $1 : [] }
    | ProofList 'n' Expr      { $3 : $1 }
    
Expr
    : Disjunct                { $1 }
    | Disjunct '->' Expr      { Implication $1 $3 }

Disjunct
    : Conjunct                { $1 }
    | Disjunct '|' Conjunct   { Disjunction $1 $3 }
    
Conjunct
    : Un                      { $1 }
    | Conjunct '&' Un         { Conjunction $1 $3 }

Un
    : 'p'                     { Predicate $1  [] }
    | 'p' '(' TermList ')'    { Predicate $1  $3 }
    | Ter '=' Ter             { Predicate "=" [$1, $3] }
    | '!' Un                  { Not $2 }
    | '(' Expr ')'            { $2 }
    | Quant 'v' Un            { Quantifier $1 $2 $3 }
    | '~' 'p'                 { Scheme $2 }

TermList
    : Ter                     { $1 : [] }
    | TermList ',' Ter        { $3 : $1 }

Quant
    : '@'                     { All }
    | '?'                     { Ex }

Ter
    : Addendum                { $1 }
    | Ter '+' Addendum        { Sum $1 $3 }

Addendum
    : Mul                     { $1 }
    | Addendum '*' Mul        { Production $1 $3 }

Mul
    : 'v'                     { Var $1 }
    | 'v' '(' TermList ')'    { Function $1 $3 }
    | '(' Ter ')'             { $2 }
    | '0'                     { Zero }
    | Mul '\''                { Hatch $1 }

{

data File4 = File4 Header Proof
data Header = Hdr [Expression] Expression
type Proof = [Expression]

data QType = All | Ex deriving Eq
data Expression  = Implication Expression Expression
                 | Disjunction Expression Expression
                 | Conjunction Expression Expression
                 | Predicate String [Term]
                 | Not Expression 
                 | Quantifier QType String Expression 
                 | Scheme String
                 deriving Eq
data Term = Sum Term Term
          | Production Term Term
          | Function String [Term]
          | Var String
          | Zero
          | Hatch Term
          deriving Eq

walkTerm :: (String -> s) -> s -> (Term -> [s] -> s) -> Term -> s
walkTerm transform zero merge term@(Sum t1 t2) = merge term [walkTerm transform zero merge t1, walkTerm transform zero merge t2]
walkTerm transform zero merge term@(Production t1 t2) = merge term [walkTerm transform zero merge t1, walkTerm transform zero merge t2]
walkTerm transform zero merge term@(Function _ ts) = merge term $ map (walkTerm transform zero merge) ts
walkTerm transform zero merge term@(Var s) = transform s
walkTerm transform zero merge term@(Zero) = zero
walkTerm transform zero merge term@(Hatch t) = merge term [walkTerm transform zero merge t]

walk :: (Term -> s) -> (Expression -> [s] -> s) -> Expression -> s
walk transform merge exp@(Implication e1 e2) = merge exp [walk transform merge e1, walk transform merge e2]
walk transform merge exp@(Disjunction e1 e2) = merge exp [walk transform merge e1, walk transform merge e2]
walk transform merge exp@(Conjunction e1 e2) = merge exp [walk transform merge e1, walk transform merge e2]
walk transform merge exp@(Predicate _ ts) = merge exp $ map transform ts
walk transform merge exp@(Not e) = merge exp [walk transform merge e]
walk transform merge exp@(Quantifier q var e) = merge exp [walk transform merge e]

freedomOfVariables :: Expression -> (DS.Set String, DS.Set String)
freedomOfVariables = walk (\t -> (DS.empty, wt t)) merge where
    wt = walkTerm DS.singleton DS.empty (\_ lst -> DS.unions lst)
    merge (Quantifier _ v _) lst = (\(t, f) -> (DS.insert v t, DS.delete v f)) (fld lst)
    merge _ lst = fld lst
    fld = foldl (\(at, af) (nt, nf) -> (DS.union at nt, DS.union af nf)) (DS.empty, DS.empty)

boundedVariables = fst . freedomOfVariables

freeVariables = snd . freedomOfVariables

isVariableFree var exp = not $ DS.member var (boundedVariables exp)

parseExpression = happilyParseExpression . alexScanTokens
parseFile4 = happilyParseFile4 . alexScanTokens

-- substituteVariable :: String -> String -> Expression -> Expression
-- substituteVariable from to = walk wt (\_ s -> if from == s then to else s) up where
    -- up :: Expression -> [Expression] -> Expression
    -- up (Implication a b) [c, d] = Implication c d
    -- up (Disjunction a b) [c, d] = Disjunction c d
    -- up (Conjunction a b) [c, d] = Conjunction c d
    -- up (Predicate name _) terms = Predicate name terms
    -- up (Not exp) [e] = Not e
    -- up (Quantifier q _ _) [v,e] = Quantifier q v e
    -- up (Scheme _) _ = undefined
    -- wt = walkTerm trans Zero upT
    -- trans s = Var $ if s == from then to else s
    -- upT (Sum _ _) [t1, t2] = Sum t1 t2
    -- upT (Production _ _) [t1, t2] = Production t1 t2
    -- upT (Function name _) ts = Function name ts
    -- upT (Hatch _) [t] = Hatch t

instance Show Term where
    show (Sum a b@(Sum _ _)) = (show a) ++ "+(" ++ (show b) ++ ")"
    show (Sum a b) = (show a) ++ "+" ++ (show b)
    show (Production a@(Sum _ _) b@(Sum _ _)) = "(" ++ (show a) ++ ")*(" ++ (show a) ++ ")"
    show (Production a@(Sum _ _) b@(Production _ _)) = "(" ++ (show a) ++ ")*(" ++ (show a) ++ ")"
    show (Production a@(Sum _ _) b) = "(" ++ (show a) ++ ")*" ++ (show a)
    show (Production a b@(Sum _ _)) = (show a) ++ "*(" ++ (show a) ++ ")"
    show (Production a b@(Production _ _)) = (show a) ++ "*(" ++ (show a) ++ ")"
    show (Production a b) = (show a) ++ "*" ++ (show a)
    show (Function name terms) = name ++ "(" ++ (intercalate "," $ map show terms) ++ ")"
    show (Var s) = s
    show (Zero) = "0"
    show (Hatch t@(Sum _ _)) = "(" ++ (show t) ++ ")'"
    show (Hatch t@(Production _ _)) = "(" ++ (show t) ++ ")'"
    show (Hatch t) = (show t) ++ "'"

instance Show Expression where
    show (Implication a@(Implication _ _) b) = "(" ++ (show a) ++ ")->" ++ (show b)
    show (Implication a b) = (show a) ++ "->" ++ (show b)
    show (Disjunction a@(Implication _ _) b@(Implication _ _)) = "(" ++ (show a) ++ ")&(" ++ (show b) ++ ")"
    show (Disjunction a@(Implication _ _) b@(Disjunction _ _)) = "(" ++ (show a) ++ ")&(" ++ (show b) ++ ")"
    show (Disjunction a@(Implication _ _) b)                   = "(" ++ (show a) ++ ")&" ++ (show b)
    show (Disjunction a b@(Implication _ _)) = (show a) ++ "&(" ++ (show b) ++ ")"
    show (Disjunction a b@(Disjunction _ _)) = (show a) ++ "&(" ++ (show b) ++ ")"
    show (Disjunction a b)                   = (show a) ++ "&" ++ (show b)
    show (Conjunction a@(Implication _ _) b@(Implication _ _)) = "(" ++ (show a) ++ ")&(" ++ (show b) ++ ")"
    show (Conjunction a@(Implication _ _) b@(Disjunction _ _)) = "(" ++ (show a) ++ ")&(" ++ (show b) ++ ")"
    show (Conjunction a@(Implication _ _) b@(Conjunction _ _)) = "(" ++ (show a) ++ ")&(" ++ (show b) ++ ")"
    show (Conjunction a@(Implication _ _) b) = "(" ++ (show a) ++ ")&" ++ (show b)
    show (Conjunction a@(Disjunction _ _) b@(Implication _ _)) = "(" ++ (show a) ++ ")&(" ++ (show b) ++ ")"
    show (Conjunction a@(Disjunction _ _) b@(Disjunction _ _)) = "(" ++ (show a) ++ ")&(" ++ (show b) ++ ")"
    show (Conjunction a@(Disjunction _ _) b@(Conjunction _ _)) = "(" ++ (show a) ++ ")&(" ++ (show b) ++ ")"
    show (Conjunction a@(Disjunction _ _) b) = "(" ++ (show a) ++ ")&" ++ (show b)
    show (Conjunction a b@(Implication _ _)) = (show a) ++ "&(" ++ (show b) ++ ")"
    show (Conjunction a b@(Disjunction _ _)) = (show a) ++ "&(" ++ (show b) ++ ")"
    show (Conjunction a b@(Conjunction _ _)) = (show a) ++ "&(" ++ (show b) ++ ")"
    show (Conjunction a b) = (show a) ++ "&" ++ (show b)
    show (Predicate name []) = name
    show (Predicate "=" [a,b]) = (show a) ++ "=" ++ (show b)
    show (Predicate name terms) = name ++ "(" ++ (intercalate "," $ map show terms) ++ ")"
    show (Not e@(Implication _ _)) = "!(" ++ (show e) ++ ")"
    show (Not e@(Disjunction _ _)) = "!(" ++ (show e) ++ ")"
    show (Not e@(Conjunction _ _)) = "!(" ++ (show e) ++ ")"
    show (Not e) = '!':(show e)
    show (Quantifier q var e@(Implication _ _)) = (show q) ++ var ++ '(':(show e) ++ ")"
    show (Quantifier q var e@(Disjunction _ _)) = (show q) ++ var ++ '(':(show e) ++ ")"
    show (Quantifier q var e@(Conjunction _ _)) = (show q) ++ var ++ '(':(show e) ++ ")"
    show (Quantifier q var e) = (show q) ++ var ++ (show e)
    show (Scheme s) = '~':s

instance Show QType where
    show (All) = "@"
    show (Ex)  = "?"

instance Show Header where
    show (Hdr pre exp) = (intercalate "," (map show pre)) ++ "|-" ++ (show exp)

instance Show File4 where
    show (File4 hdr list) = (show hdr) ++ ('\n':(intercalate "\n" (map show list)))

}
