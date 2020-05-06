{
module Parser where

import Lexer
import Types
}

%name parse
%tokentype { Token }
%error { parseError }

%token
    '|-'        { TTurnstile }
    ','         { TComma }
    '('         { TOpenBrace }
    ')'         { TCloseBrace }
    '!'         { TNot }
    '->'        { TImplication }
    '&'         { TAnd }
    '|'         { TOr }
    var         { TVariable $$ }

%left '|-'
%right ','
%right '->'
%left '|'
%left '&'
%left '!'

%%

Line
    : Context '|-' Exp   { FirstLine ($1, $3) }
    | '|-' Exp           { FirstLine ([], $2) }
    | Exp                { Line $1 }

Context
    : Exp ',' Context    { $1 : $3 }
    | Exp                { [$1] }

Exp  : '!' Exp              { Not $2 }
     | Exp '->' Exp         { Operation Impl $1 $3}
     | Exp '&' Exp          { Operation And $1 $3 }
     | Exp '|' Exp          { Operation Or $1 $3 }
     | '(' Exp ')'          { $2 }
     | var                  { Variable $1 }

{
parseError = error "Parse error"
}
