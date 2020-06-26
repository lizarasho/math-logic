{
module Parser where

import Lexer
import Types
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

Line : Exp                { ProofLine $1 }

Exp  : '!' Exp              { Not $2 }
     | Exp '->' Exp         { $1 :->: $3 }
     | Exp '&' Exp          { $1 :&: $3 }
     | Exp '|' Exp          { $1 :|: $3 }
     | '(' Exp ')'          { $2 }
     | var                  { Variable $1 }

{
parseError = error "Parse error"
}