{
module MathlogicTokens where
}

%wrapper "basic"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-

  ($white # \n)+            ;
  "->"                      { \s -> Impl }
  "|"                       { \s -> Disj }
  "&"                       { \s -> Conj }
  "("                       { \s -> LB }
  ")"                       { \s -> RB }
  "!"                       { \s -> No }
  ","                       { \s -> Comma }
  "|-"                      { \s -> EOP }
  \n                        { \s -> NL }
  $alpha [$alpha $digit]*   { \s -> PV s }

{
-- Each action has type :: String -> Token

-- The token type:
data Symbol =
    PV String |
    Impl      |
    Conj      |
    Disj      |
    LB        |
    RB        |
    No        |
    Comma     |
    EOP       |
    NL
    deriving (Eq,Show)

test = do
  s <- getContents
  print (alexScanTokens s)
}
