module Types where

data Line = Header Exp | ProofLine { getLineExp :: Exp }   

data Exp =  Exp Pred | Not Exp |  Term :@: Exp | Term :?: Exp | Exp :->: Exp | Exp :&: Exp | Exp :|: Exp
    deriving Ord

type Variable = String    

data Pred = Pred Variable | Term :=: Term
    deriving Ord

data Term = Term Variable | Zero | Succ Term | Term :+: Term | Term :*: Term 
    deriving Ord

instance Eq Pred where
    Pred p == Pred p' = p == p'
    u :=: v == u' :=: v' = u == u' && v == v'
    _ == _ = False    

instance Eq Exp where
    Exp p == Exp p' = p == p'
    Not e == Not e' = e == e'
    (:@:) v e == (:@:) v' e' = v == v' && e == e'
    (:?:) v e == (:?:) v' e' = v == v' && e == e'
    u :->: v == u' :->: v' = u == u' && v == v' 
    u :&: v == u' :&: v' = u == u' && v == v'     
    u :|: v == u' :|: v' = u == u' && v == v' 
    _ == _ = False   

instance Eq Term where 
    Term v == Term v' = v == v'
    Succ t == Succ t' = t == t'
    u :+: v == u' :+: v' = u == u' && v == v'
    u :*: v == u' :*: v' = u == u' && v == v'
    Zero == Zero = True
    _ == _ = False     

instance Show Line where
    show (Header e) = "|-" ++ show e
    show (ProofLine e) = show e 
    
instance Show Exp where
    show (Exp p) = show p  
    show (Not e) = "(!" ++ show e ++ ")"
    show ((:@:) v e) = "(@" ++ show v ++ "." ++ show e ++ ")"
    show ((:?:) v e) = "(?" ++ show v ++ "." ++ show e ++ ")"
    show (u :->: v) = "(" ++ show u ++ "->" ++ show v ++ ")"
    show (u :&: v) = "(" ++ show u ++ "&" ++ show v ++ ")"
    show (u :|: v) = "(" ++ show u ++ "|" ++ show v ++ ")"    

instance Show Pred where
    show (Pred v) = v    
    show (u :=: v) = "(" ++ show u ++ "=" ++ show v ++ ")"

instance Show Term where
    show (Term v) = v
    show Zero = "0"
    show (Succ t) = show t ++ "\'"  
    show (u :+: v) = "(" ++ show u ++ "+" ++ show v ++ ")"
    show (u :*: v) = "(" ++ show u ++ "*" ++ show v ++ ")"    



