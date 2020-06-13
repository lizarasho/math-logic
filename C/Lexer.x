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
    "@"               { \_ -> TForall }
    "?"               { \_ -> TExists }
    "="               { \_ -> TEquals }
    "."               { \_ -> TDot }
    "+"               { \_ -> TPlus }
    "*"               { \_ -> TAsterisk }
    "0"               { \_ -> TZero }
    "'"              { \_ -> TSucc }
    [a-z]             { \id -> TVar id }
    [A-Z]             { \id -> TPred id }

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
     | TDot
     | TPlus
     | TAsterisk
     | TZero
     | TForall
     | TExists
     | TEquals
     | TSucc
     | TVar String
     | TPred String
     deriving (Show)
}