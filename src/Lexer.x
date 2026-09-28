{
module Lexer
  ( Token(..)
  , scanTokens
  ) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z_]
$identchar = [a-zA-Z0-9_']
$white = [\ \t\n\r]

tokens :-

  $white+               ;
  "//".*                ;
  "--".*                ;
  "/*"($white|[^\*\ \t\n\r]|\*+[^\/\*])*\*+"/" ;

  "[||]"                { \_ -> TokenEmptyTypeRecord }
  "[]"                  { \_ -> TokenEmptyTermRecord }
  "[|"                  { \_ -> TokenLBracketBar }
  "|]"                  { \_ -> TokenBarRBracket }
  "::"                  { \_ -> TokenDColon }
  ":="                  { \_ -> TokenAssign }
  "->"                  { \_ -> TokenArrow }
  "=="                  { \_ -> TokenDoubleEq }
  "||"                  { \_ -> TokenOr }
  "&&"                  { \_ -> TokenAnd }

  "("                   { \_ -> TokenLParen }
  ")"                   { \_ -> TokenRParen }
  "()"                  { \_ -> TokenUnit }
  "{"                   { \_ -> TokenLBrace }
  "}"                   { \_ -> TokenRBrace }
  "|"                   { \_ -> TokenPipe }
  "."                   { \_ -> TokenDot }
  ","                   { \_ -> TokenComma }
  ":"                   { \_ -> TokenColon }
  "="                   { \_ -> TokenEq }
  "@"                   { \_ -> TokenAt }
  "^"                   { \_ -> TokenCaret }
  "`"                   { \_ -> TokenTick }
  "["                   { \_ -> TokenLBracket }
  "]"                   { \_ -> TokenRBracket }
  "!"                   { \_ -> TokenDeref }

  "uninterp"            { \_ -> TokenRetiredLogicalCall }
  "forall"              { \_ -> TokenForall }
  "letrec"              { \_ -> TokenLetRec }
  "let"                 { \_ -> TokenLet }
  "tfun"                { \_ -> TokenTLambda }
  "fun"                 { \_ -> TokenLambda }
  "if"                  { \_ -> TokenIf }
  "then"                { \_ -> TokenThen }
  "else"                { \_ -> TokenElse }
  "new"                 { \_ -> TokenNew }
  "in"                  { \_ -> TokenIn }
  "Pi"                  { \_ -> TokenPi }

  "KType"               { \_ -> TokenKType }
  "KBool"               { \_ -> TokenKBool }
  "KLabel"              { \_ -> TokenKLabel }
  "KRec"                { \_ -> TokenKRec }
  "KFun"                { \_ -> TokenKFun }
  "KRef"                { \_ -> TokenKRef }
  "KCol"                { \_ -> TokenKCol }
  "KGen"                { \_ -> TokenKGen }

  "headLabel"           { \_ -> TokenHeadLabel }
  "head"                { \_ -> TokenHead }
  "tail"                { \_ -> TokenTail }
  "dom"                 { \_ -> TokenDom }
  "img"                 { \_ -> TokenCod }
  "refOf"               { \_ -> TokenRefOf }
  "colOf"               { \_ -> TokenColOf }
  "empty"               { \_ -> TokenEmpty }
  "labels"              { \_ -> TokenLabSet }
  "#"                   { \_ -> TokenApart }
  "subset"              { \_ -> TokenSubset }
  "member"              { \_ -> TokenMember }
  "not"                 { \_ -> TokenNot }
  "TUnit"               { \_ -> TokenTUnit }
  "TInt"                { \_ -> TokenIntType }
  "TBool"               { \_ -> TokenBoolType }
  "TString"             { \_ -> TokenStringType }
  "TRef"                { \_ -> TokenTRef }
  "TCol"                { \_ -> TokenTCol }
  "True"                { \_ -> TokenTrue }
  "False"               { \_ -> TokenFalse }
  "KTrue"               { \_ -> TokenKTrue }
  "KFalse"              { \_ -> TokenKFalse }

  $digit+               { \s -> TokenInteger (read s) }
  \" [^\"]* \"          { \s -> TokenString (init (tail s)) }
  $alpha $identchar*    { \s -> TokenName s }

{
data Token
  = TokenLParen | TokenRParen
  | TokenRetiredLogicalCall
  | TokenLBrace | TokenRBrace | TokenPipe
  | TokenLBracketBar | TokenBarRBracket
  | TokenLBracket | TokenRBracket | TokenEmptyTypeRecord | TokenEmptyTermRecord
  | TokenDot | TokenComma | TokenColon | TokenDColon
  | TokenEq | TokenDoubleEq | TokenAt | TokenCaret | TokenTick
  | TokenArrow | TokenAssign | TokenDeref
  | TokenLambda | TokenTLambda | TokenForall
  | TokenLet | TokenLetRec | TokenIn
  | TokenIf | TokenThen | TokenElse
  | TokenNew
  | TokenLabSet
  | TokenPi
  | TokenKType | TokenKBool | TokenKLabel | TokenKRec | TokenKFun
  | TokenKRef | TokenKCol | TokenKGen
  | TokenUnit | TokenTUnit | TokenIntType | TokenBoolType | TokenStringType
  | TokenTRef | TokenTCol | TokenTrue | TokenFalse | TokenKTrue | TokenKFalse
  | TokenHead | TokenHeadLabel | TokenTail | TokenDom | TokenCod
  | TokenRefOf | TokenColOf | TokenEmpty
  | TokenApart | TokenSubset | TokenMember | TokenNot | TokenAnd | TokenOr
  | TokenInteger !Int | TokenString !String | TokenName !String
  deriving (Eq, Show)

scanTokens :: String -> Either String [Token]
scanTokens source = scan ('\n', [], source)
  where
    scan input@(_, _, remaining) = case alexScan input 0 of
      AlexEOF -> Right []
      AlexError (_, _, rest) -> Left ("Lexical error near: " ++ take 24 rest)
      AlexSkip next _ -> scan next
      AlexToken next count token -> (token (take count remaining) :) <$> scan next
}
