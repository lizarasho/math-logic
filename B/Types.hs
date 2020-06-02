module Types where

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

data Line = Header (Context, Exp) | Line { getLineExp :: Exp }

instance Show Line where
    show (Header ([], exp)) = "|- " ++ (show exp)
    show (Header (c, exp)) = (helper c) ++ " |- " ++ (show exp) where
        helper [] = []
        helper [e] = show e
        helper (e : es) = (show e) ++ ", " ++ (helper es)

type Context = [Exp]