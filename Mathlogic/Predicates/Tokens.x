
{
module Mathlogic.Predicates.Tokens where
}

%wrapper "basic"

$digit = 0-9			-- digits

tokens :-

  ($white # \n)+            ;
  "~"                       { \s -> Magic }
  "->"                      { \s -> Impl }
  "|"                       { \s -> Disj }
  "&"                       { \s -> Conj }
  "("                       { \s -> LB }
  ")"                       { \s -> RB }
  "!"                       { \s -> No }
  "@"                       { \s -> ForAll }
  "?"                       { \s -> Exists }
  "="                       { \s -> Equals }
  "+"                       { \s -> Add }
  "*"                       { \s -> Multiply }
  "'"                       { \s -> Hatch' }
  "0"                       { \s -> Zero' }
  ","                       { \s -> Comma }
  "|-"                      { \s -> EOP }
  \n                        { \s -> NL }
  [a-z] [$digit]*           { \s -> Fun s }
  [A-Z] [$digit]*           { \s -> Pred s }

{
-- Each action has type :: String -> Token

-- The token type:
data Symbol =
    Magic       |
    Fun String  |
    Pred String |
    Impl        |
    Conj        |
    Disj        |
    LB          |
    RB          |
    No          |
    ForAll      |
    Exists      |
    Equals      |
    Add         |
    Multiply    |
    Hatch'      |
    Zero'       |
    Comma       |
    EOP         |
    NL
    deriving (Eq,Show)

test = do
  s <- getContents
  print (alexScanTokens s)
}
