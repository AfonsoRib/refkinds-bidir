{
module Parser
  ( parseSurfaceExpr
  , parseSurfaceType
  , parseSurfaceKind
  , parseSurfacePred
  , parseExpr
  , parseType
  , parseKind
  , parsePred
  ) where

import qualified Desugar as D
import qualified Lexer as L
import qualified Types as T
}

%name parseSurfaceExprTop expr
%name parseSurfaceTypeTop typeExpr
%name parseSurfaceKindTop kindExpr
%name parseSurfacePredTop predExpr

%tokentype { L.Token }
%monad { Either String } { (>>=) } { return }
%error { parseError }
%expect 0

%token
  or           { L.TokenOr }
  lparen       { L.TokenLParen }
  rparen       { L.TokenRParen }
  lbrace       { L.TokenLBrace }
  rbrace       { L.TokenRBrace }
  pipe         { L.TokenPipe }
  lbracketbar  { L.TokenLBracketBar }
  barrbracket  { L.TokenBarRBracket }
  lbracket     { L.TokenLBracket }
  rbracket     { L.TokenRBracket }
  emptytyperecord { L.TokenEmptyTypeRecord }
  emptytermrecord { L.TokenEmptyTermRecord }
  dot          { L.TokenDot }
  comma        { L.TokenComma }
  colon        { L.TokenColon }
  dcolon       { L.TokenDColon }
  eq           { L.TokenEq }
  doubleeq     { L.TokenDoubleEq }
  at           { L.TokenAt }
  caret        { L.TokenCaret }
  tick         { L.TokenTick }
  arrow        { L.TokenArrow }
  assign       { L.TokenAssign }
  deref        { L.TokenDeref }
  lambda       { L.TokenLambda }
  tlambda      { L.TokenTLambda }
  forall       { L.TokenForall }
  let          { L.TokenLet }
  letrec       { L.TokenLetRec }
  in           { L.TokenIn }
  if           { L.TokenIf }
  then         { L.TokenThen }
  else         { L.TokenElse }
  new          { L.TokenNew }
  pi           { L.TokenPi }
  ktype        { L.TokenKType }
  kbool        { L.TokenKBool }
  klabel       { L.TokenKLabel }
  krec         { L.TokenKRec }
  kfun         { L.TokenKFun }
  kref         { L.TokenKRef }
  kcol         { L.TokenKCol }
  kgen         { L.TokenKGen }
  tunit        { L.TokenUnit }
  ttunit       { L.TokenTUnit }
  tint         { L.TokenIntType }
  tbool        { L.TokenBoolType }
  tstring      { L.TokenStringType }
  ttrue        { L.TokenTrue }
  tfalse       { L.TokenFalse }
  kttrue       { L.TokenKTrue }
  ktfalse      { L.TokenKFalse }
  head         { L.TokenHead }
  headlabel    { L.TokenHeadLabel }
  tail         { L.TokenTail }
  dom          { L.TokenDom }
  cod          { L.TokenCod }
  tref         { L.TokenTRef }
  refof        { L.TokenRefOf }
  tcol         { L.TokenTCol }
  colof        { L.TokenColOf }
  empty        { L.TokenEmpty }
  apart        { L.TokenApart }
  subset       { L.TokenSubset }
  member       { L.TokenMember }
  not          { L.TokenNot }
  and          { L.TokenAnd }
  labset       { L.TokenLabSet }
  intVal       { L.TokenInteger $$ }
  strVal       { L.TokenString $$ }
  name         { L.TokenName $$ }

%%

expr :: { T.SExpr }
  : lambda name arrow expr                  { T.SELambda $2 $4 }
  | tlambda name arrow expr                 { T.SETLambda $2 $4 }
  | let name eq expr in expr                 { T.SELet $2 $4 $6 }
  | let name colon typeExpr eq expr in expr  { T.SELet $2 (T.SEAnn $6 $4) $8 }
  | letrec name colon typeExpr eq expr in expr { T.SELetRec $2 $4 $6 $8 }
  | if expr then expr else expr              { T.SEIf $2 $4 $6 }
  | appExpr assign appExpr                  { T.SEAssign $1 $3 }
  | appExpr at appExpr                      { T.SEConcat $1 $3 }
  | appExpr caret expr                      { T.SEStringConcat $1 $3 }
  | appExpr colon typeExpr                  { T.SEAnn $1 $3 }
  | appExpr                                 { $1 }

appExpr :: { T.SExpr }
  : appExpr atomExpr                        { T.SEApp $1 $2 }
  | appExpr lbracket typeExpr rbracket      { T.SETApp $1 $3 }
  | atomExpr                                { $1 }

atomExpr :: { T.SExpr }
  : tunit                                   { T.SEUnit }
  | intVal                                  { T.SEInteger $1 }
  | strVal                                  { T.SEString $1 }
  | ttrue                                   { T.SEBoolean True }
  | tfalse                                  { T.SEBoolean False }
  | name                                    { T.SEVar $1 }
  | tick name                               { T.SELabel $2 }
  | emptytermrecord                         { T.SERecordNil }
  | lbracket rbracket                       { T.SERecordNil }
  | head atomExpr                           { T.SEHead $2 }
  | headlabel atomExpr                      { T.SEHeadLabel $2 }
  | tail atomExpr                           { T.SETail $2 }
  | new atomExpr                            { T.SERef $2 }
  | deref atomExpr                          { T.SERefOf $2 }
  | not atomExpr                            { T.SENot $2 }
  | lbracket recordFieldsExpr rbracket      { $2 }
  | lparen expr rparen                      { $2 }

recordFieldsExpr :: { T.SExpr }
  : name eq expr comma recordFieldsExpr     { T.SERecordCons $1 $3 $5 }
  | tick name eq expr comma recordFieldsExpr { T.SERecordCons $2 $4 $6 }
  | name eq expr pipe expr                  { T.SERecordCons $1 $3 $5 }
  | tick name eq expr pipe expr             { T.SERecordCons $2 $4 $6 }
  | name eq expr                            { T.SERecordCons $1 $3 T.SERecordNil }
  | tick name eq expr                       { T.SERecordCons $2 $4 T.SERecordNil }

typeExpr :: { T.SType }
  : lambda name arrow typeExpr              { T.STLambda $2 $4 }
  | tlambda name arrow typeExpr             { T.STLambda $2 $4 }
  | forall name dcolon kindExpr dot typeExpr { T.STForall $2 $4 $6 }
  | let name eq typeExpr in typeExpr { T.STLet (T.SDecl $2 $4) $6 }
  | let name dcolon kindExpr eq typeExpr in typeExpr { T.STLet (T.SDecl $2 (T.STAnn $6 $4)) $8 }
  | letrec name dcolon kindExpr eq typeExpr in typeExpr { T.STRec $2 (T.STAnn $6 $4) $8 }
  | if typeExpr then typeExpr else typeExpr { T.STIf $2 $4 $6 }
  | arrowType                               { $1 }

-- Tightest first: application/unary, equality/membership, conjunction,
-- disjunction, then arrow or a whole-type kind annotation. Implication and
-- equivalence belong solely to the first-order predicate grammar below.
arrowType :: { T.SType }
  : orType arrow typeExpr                   { T.STArrow $1 $3 }
  | orType dcolon kindExpr                  { T.STAnn $1 $3 }
  | orType                                  { $1 }

orType :: { T.SType }
  : orType or andType                      { T.STOr $1 $3 }
  | andType                                 { $1 }

andType :: { T.SType }
  : andType and relationType               { T.STAnd $1 $3 }
  | relationType                            { $1 }

relationType :: { T.SType }
  : appType at appType                     { T.STConcat $1 $3 }
  | appType doubleeq appType               { T.STEq $1 $3 }
  | appType                                 { $1 }

appType :: { T.SType }
  : appType atomType                        { T.STApp $1 $2 }
  | atomType                                { $1 }

atomType :: { T.SType }
  : ttunit                                  { T.STUnit }
  | tint                                    { T.STInt }
  | tbool                                   { T.STBool }
  | tstring                                 { T.STString }
  | kttrue                                  { T.STTrue }
  | ktfalse                                 { T.STFalse }
  | strVal                                  { T.STLabel $1 }
  | name                                    { T.STVar $1 }
  | tick name                               { T.STLabel $2 }
  | head atomType                           { T.STHead $2 }
  | headlabel atomType                      { T.STHeadLabel $2 }
  | tail atomType                           { T.STTail $2 }
  | dom atomType                            { T.STDom $2 }
  | cod atomType                            { T.STImg $2 }
  | tref atomType                           { T.STRef $2 }
  | refof atomType                          { T.STRefOf $2 }
  | tcol atomType                           { T.STCol $2 }
  | colof atomType                          { T.STColOf $2 }
  | empty atomType                          { T.STEmpty $2 }
  | not atomType                            { T.STNot $2 }
  | emptytyperecord                         { T.STRecNil }
  | lbracketbar recordFieldsType barrbracket { $2 }
  | lparen typeExpr rparen                  { $2 }

recordFieldsType :: { T.SType }
  : fieldLabel colon typeExpr comma recordFieldsType { T.STRecCons $1 $3 $5 }
  | fieldLabel colon typeExpr pipe typeExpr  { T.STRecCons $1 $3 $5 }
  | fieldLabel colon typeExpr                { T.STRecCons $1 $3 T.STRecNil }

fieldLabel :: { T.SType }
  : tick name                               { T.STLabel $2 }
  | strVal                                  { T.STLabel $1 }
  | name                                    { T.STVar $1 }
  | headlabel atomType                      { T.STHeadLabel $2 }

kindExpr :: { T.SKind }
  : pi name dcolon kindExpr dot kindExpr    { T.SKPi $2 $4 $6 }
  | kgen name dcolon kindExpr dot kindExpr  { T.SKGen $2 $4 $6 }
  | kindArrow                               { $1 }

kindArrow :: { T.SKind }
  : kindPrimary arrow kindExpr              { T.SKPi "_" $1 $3 }
  | kindPrimary                             { $1 }

kindPrimary :: { T.SKind }
  : lbrace name dcolon baseKind pipe predExpr rbrace { T.SKBase $4 (T.SRefined $2 $6) }
  | baseKind                                { surfaceTrueKind $1 }
  | lparen kindExpr rparen                  { $2 }

baseKind :: { T.SBaseKind }
  : ktype                                   { T.SBKType }
  | kbool                                   { T.SBKBool }
  | klabel                                  { T.SBKLabel }
  | krec                                    { T.SBKRec }
  | kfun                                    { T.SBKFun }
  | kref                                    { T.SBKRef }
  | kcol                                    { T.SBKCol }

predExpr :: { T.SPred }
  : arrowPred { $1 }

arrowPred :: { T.SPred }
  : orPred arrow predExpr                   { T.SPArrow $1 $3 }
  | orPred                                  { $1 }

orPred :: { T.SPred }
  : orPred or andPred                      { T.binarySurfacePredOp T.BOr $1 $3 }
  | andPred                                 { $1 }

andPred :: { T.SPred }
  : andPred and relationPred               { T.binarySurfacePredOp T.BAnd $1 $3 }
  | relationPred                            { $1 }

relationPred :: { T.SPred }
  : appPred at appPred                     { T.binarySurfacePredOp T.BConcat $1 $3 }
  | appPred doubleeq appPred               { T.binarySurfacePredOp T.BEq $1 $3 }
  | appPred member appPred                 { T.SPMember $1 (predicateLabels $3) }
  | appPred apart appPred                  { T.SPApart (predicateLabels $1) (predicateLabels $3) }
  | appPred                                 { $1 }

appPred :: { T.SPred }
  : apart atomPred atomPred                 { T.SPApart (predicateLabels $2) (predicateLabels $3) }
  | member atomPred atomPred                { T.SPMember $2 (predicateLabels $3) }
  | subset atomPred atomPred                { T.SPSubset
                                                (predicateLabels $2)
                                                (predicateLabels $3) }
  | atomPred                                { $1 }

atomPred :: { T.SPred }
  : ttunit                                  { T.SPUnit }
  | tint                                    { T.SPInt }
  | tbool                                   { T.SPBool }
  | tstring                                 { T.SPString }
  | kttrue                                  { T.SPTrue }
  | ktfalse                                 { T.SPFalse }
  | strVal                                  { T.SPLabel $1 }
  | name                                    { T.SPVar $1 }
  | tick name                               { T.SPLabel $2 }
  | head atomPred                           { T.unarySurfacePredOp T.BHead $2 }
  | headlabel atomPred                      { T.unarySurfacePredOp T.BHeadLabel $2 }
  | tail atomPred                           { T.unarySurfacePredOp T.BTail $2 }
  | dom atomPred                            { T.unarySurfacePredOp T.BDom $2 }
  | cod atomPred                            { T.unarySurfacePredOp T.BImg $2 }
  | tref atomPred                           { T.SPRef $2 }
  | refof atomPred                          { T.unarySurfacePredOp T.BRefOf $2 }
  | tcol atomPred                           { T.SPCol $2 }
  | colof atomPred                          { T.unarySurfacePredOp T.BColOf $2 }
  | empty atomPred                          { T.unarySurfacePredOp T.BEmpty $2 }
  | not atomPred                            { T.unarySurfacePredOp T.BNot $2 }
  | labset atomPred                         { T.SPLabSet $2 }
  | emptytyperecord                         { T.SPRecNil }
  | lbracketbar recordFieldsPred barrbracket { $2 }
  | lparen predExpr rparen                  { $2 }

recordFieldsPred :: { T.SPred }
  : predFieldLabel colon predExpr comma recordFieldsPred { T.SPRecCons $1 $3 $5 }
  | predFieldLabel colon predExpr pipe predExpr  { T.SPRecCons $1 $3 $5 }
  | predFieldLabel colon predExpr                { T.SPRecCons $1 $3 T.SPRecNil }

predFieldLabel :: { T.SPred }
  : tick name                               { T.SPLabel $2 }
  | strVal                                  { T.SPLabel $1 }
  | name                                    { T.SPVar $1 }
  | headlabel atomPred                      { T.unarySurfacePredOp T.BHeadLabel $2 }



{
predicateLabels :: T.SPred -> T.SPred
predicateLabels p@T.SPLabSet {} = p

predicateLabels p = T.SPLabSet p

surfaceTrueKind :: T.SBaseKind -> T.SKind
surfaceTrueKind = T.SKPlain

parseError :: [L.Token] -> Either String a
parseError toks = Left ("Parse error at tokens: " ++ show (take 10 toks))

parseSurfaceExpr :: String -> Either String T.SExpr
parseSurfaceExpr s = do
  toks <- L.scanTokens s
  parseSurfaceExprTop toks

parseSurfaceType :: String -> Either String T.SType
parseSurfaceType s = do
  toks <- L.scanTokens s
  parseSurfaceTypeTop toks

parseSurfaceKind :: String -> Either String T.SKind
parseSurfaceKind s = do
  toks <- L.scanTokens s
  parseSurfaceKindTop toks

parseSurfacePred :: String -> Either String T.SPred
parseSurfacePred s = do
  toks <- L.scanTokens s
  parseSurfacePredTop toks

parseExpr :: String -> Either String T.Expr
parseExpr = fmap D.lowerExpr . parseSurfaceExpr

parseType :: String -> Either String T.Type
parseType = fmap D.lowerType . parseSurfaceType

parseKind :: String -> Either String T.Rkind
parseKind = fmap D.lowerKind . parseSurfaceKind

parsePred :: String -> Either String T.Pred
parsePred = fmap D.lowerPredicate . parseSurfacePred

}
