{
module Parser where

import Lexer
}

%name parse
%tokentype { Token }
%error { parseError }

%token
    '('         { TOpenBrace }
    ')'         { TCloseBrace }
    '!'         { TNot }
    '->'        { TImplication }
    '&'         { TAnd }
    '|'         { TOr }
    var         { TVariable $$ }

%right '->'
%left '|'
%left '&'
%left '!'

%%

Vertex  : '!' Vertex              { Not $2 }
     | Vertex '->' Vertex         { Operation Implication $1 $3}
     | Vertex '&' Vertex          { Operation And $1 $3 }
     | Vertex '|' Vertex          { Operation Or $1 $3 }
     | '(' Vertex ')'             { $2 }
     | var                        { Variable $1 }

{
parseError = error "Parse error"

data Sign = Implication | Or | And
instance Show Sign where
    show Implication = "->"
    show Or = "|"
    show And = "&"

data Vertex = Variable String | Operation Sign Vertex Vertex | Not Vertex
instance Show Vertex where
    show (Variable s) = s
    show (Operation op v v') = "(" ++ (show op) ++ "," ++ (show v) ++ "," ++ (show v') ++ ")"
    show (Not v) = "(!" ++ (show v) ++ ")"
}
