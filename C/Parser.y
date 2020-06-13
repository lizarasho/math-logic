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
    '('         { TOpenBrace }
    ')'         { TCloseBrace }
    '!'         { TNot }
    '->'        { TImplication }
    '&'         { TAnd }
    '|'         { TOr }
    '@'         { TForall }
    '?'         { TExists }
    '='         { TEquals }
    '.'         { TDot }
    '+'         { TPlus }
    '*'         { TAsterisk }
    '0'         { TZero }
    '\''        { TSucc }
    var         { TVar $$ }
    pred        { TPred $$ }

%right '.'
%right '->'
%left '|'
%left '&'
%left '!'
%left '+'
%left '*'
%left '\''

%%

Line : '|-' Exp             { Header $2 }
     | Exp                  { ProofLine $1 }

Exp : Exp '->' Exp          { $1 :->: $3 }      
    | Exp '|' Exp           { $1 :|: $3 }       
    | Exp '&' Exp           { $1 :&: $3 }
    | Pred                  { Exp $1 }
    | '!' Exp               { Not $2 }
    | '(' Exp ')'           { $2 }
    | '@' var '.' Exp       { (:@:) (Term $2) $4 }
    | '?' var '.' Exp       { (:?:) (Term $2) $4 }

Pred : pred                 { Pred $1 }    
     | Term '=' Term        { $1 :=: $3 }

Term : Term '*' Term        { $1 :*: $3 }  
     | Term '+' Term        { $1 :+: $3 } 
     | '(' Term ')'         { $2 }
     | Term '\''            { Succ $1 }  
     | var                  { Term $1 }
     | '0'                  { Zero }     
    
{
parseError = error "Parse error"
}
