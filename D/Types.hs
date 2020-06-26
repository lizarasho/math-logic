module Types where

data AnnotatedExp = AxOrHyp Exp | MP Exp Int Int  deriving (Eq, Ord, Show)
getExp :: AnnotatedExp -> Exp 
getExp (AxOrHyp e) = e 
getExp (MP e _ _) = e

data Exp = Exp :&: Exp | Exp :|: Exp | Exp :->: Exp | Not Exp | Variable String 
    deriving Ord

instance Show Exp where
    show (Variable s) = s
    show (u :&: v) = "(" ++ show u ++ " & " ++ show v ++ ")"
    show (u :|: v) = "(" ++ show u ++ " | " ++ show v ++ ")"
    show (u :->: v) = "(" ++ show u ++ " -> " ++ show v ++ ")"
    show (Not v) = "!" ++ show v

instance Eq Exp where
    Variable v == Variable v' = v == v'
    u :&: v == u' :&: v' = u == u' && v == v'
    u :|: v == u' :|: v' = u == u' && v == v'
    u :->: v == u' :->: v' = u == u' && v == v'
    Not e == Not e' = e == e'
    _ == _ = False   

data Line = Header Exp | ProofLine { getLineExp :: Exp }

instance Show Line where
    show (Header e) = "|- " ++ show e
    show (ProofLine e) = show e