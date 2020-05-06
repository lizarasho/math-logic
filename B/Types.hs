module Types where

data Sign = Impl | Or | And 
    deriving (Eq, Ord)
instance Show Sign where
    show Impl = "->"
    show Or = "|"
    show And = "&"


data Exp = Variable String | Operation Sign !Exp !Exp | Not !Exp
    deriving Ord
instance Show Exp where
    show (Variable s) = s
    show (Operation op v v') = "(" ++ show v ++ " " ++ show op ++ " " ++ show v' ++ ")"
    show (Not v) = "!" ++ show v


instance Eq Exp where
    Variable v == Variable v' = v == v'
    Not e == Not e' = e == e'
    Operation s u v == Operation s' u' v' = s == s' && u == u' && v == v' 
    _ == _ = False   

data Line = FirstLine (Context, Exp) | Line { getLineExp :: Exp }

instance Show Line where
    show (FirstLine ([], exp)) = "|- " ++ (show exp)
    show (FirstLine (c, exp)) = (helper c) ++ " |- " ++ (show exp) where
        helper [] = []
        helper [e] = show e
        helper (e : es) = (show e) ++ ", " ++ (helper es)

type Context = [Exp]