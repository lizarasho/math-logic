{
module Lexer where
}

%wrapper "basic"

tokens :-
    $white+           ;
    "("               { \_ -> TOpenBrace }
    ")"               { \_ -> TCloseBrace }
    "!"               { \_ -> TNot }
    "->"              { \_ -> TImplication }
    "&"               { \_ -> TAnd }
    "|"               { \_ -> TOr }
    "|-"              { \_ -> TTurnstile }
    ","               { \_ -> TComma }
    [A-Z][A-Z0-9']*   { \id -> TVariable id }


{
data Token = 
       TOpenBrace
     | TCloseBrace
     | TTurnstile
     | TComma
     | TNot
     | TImplication
     | TOr
     | TAnd
     | TVariable String
     deriving (Show)
}