module Main where

import Lexer (alexScanTokens)
import Parser (parse)
import Types

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe (isJust, fromJust, isNothing)
import Data.Either (isLeft, isRight)

data AnnotatedExp = AxiomSch Exp String | Axiom Exp Int | MP Exp Int Int | Intro Exp Int deriving (Eq, Show)

getExp :: AnnotatedExp -> Exp
getExp (AxiomSch exp _) = exp
getExp (Axiom exp _) = exp
getExp (MP exp _ _) = exp
getExp (Intro exp _) = exp

tryAxiom :: Exp -> Maybe Int
tryAxiom ((Exp (a :=: b) :->: (Exp (a' :=: c') :->: Exp (b'' :=: c'')))) 
  | a == Term "a" && b == Term "b" && c' == Term "c" && a == a' && b == b'' && c' == c'' = Just 1
tryAxiom (Exp (a :=: b) :->: Exp (Succ a' :=: Succ b')) 
  | a == Term "a" && b == Term "b" && a == a' && b == b' = Just 2
tryAxiom (Exp (Succ a' :=: Succ b') :->: Exp (a :=: b)) 
  | a == Term "a" && b == Term "b" && a == a' && b == b' = Just 3
tryAxiom (Not (Exp (Succ a :=: Zero))) | a == Term "a" = Just 4
tryAxiom (Exp ((a :+: Zero) :=: a')) | a == Term "a" && a == a' = Just 5
tryAxiom (Exp ((a :+: Succ b) :=: Succ (a' :+: b')))
  | a == Term "a" && b == Term "b" && a == a' && b == b' = Just 6
tryAxiom (Exp ((a :*: Zero) :=: Zero)) | a == Term "a" = Just 7
tryAxiom (Exp ((a :*: Succ b) :=: ((a' :*: b') :+: a''))) 
  | a == Term "a" && b == Term "b" && a == a' && a' == a'' && b == b' = Just 8
tryAxiom _ = Nothing

tryMP :: Exp -> Map.Map Exp Int -> Map.Map Exp [(Exp, Int)] -> Maybe AnnotatedExp
tryMP exp mapExp mapTails = case Map.lookup exp mapTails of
  Just xs -> case sortBy (\(a, m) (b, n) -> flip compare (mapExp Map.! a, m) (mapExp Map.! b, n))
            $ filter (isJust . (`Map.lookup` mapExp) . fst) xs of 
    ((x'', v'') : _) -> Just $ MP exp (mapExp Map.! x'') v''
    [] -> Nothing 
  Nothing -> Nothing 

isNotProved :: String
isNotProved = "is not proved"

tryIntro :: Exp -> Map.Map Exp Int -> Either String AnnotatedExp
tryIntro exp mapExp = let
  helper :: Exp -> Exp -> Term -> Either String AnnotatedExp
  helper f h x
    | Map.member h mapExp && hasFreeOccurrence f x = Left $ "variable " ++ show x ++ " occurs free in ?@-rule"
    | Map.member h mapExp && not (hasFreeOccurrence f x) = Right $ Intro exp $ mapExp Map.! h
    | otherwise = Left isNotProved

  tryForall :: Exp  -> Either String AnnotatedExp
  tryForall (f :->: ((:@:) x g)) = helper f (f :->: g) x    
  tryForall _ = Left isNotProved

  tryExists :: Exp -> Either String AnnotatedExp
  tryExists (((:?:) x g) :->: f) = helper f (g :->: f) x
  tryExists _ = Left isNotProved
  in let 
    resForall = tryForall exp
    resExists = tryExists exp
    in if isRight resExists || isLeft resForall && resExists /= Left isNotProved
      then resExists
      else resForall

hasFreeOccurrence :: Exp -> Term -> Bool
hasFreeOccurrence (Exp p) t = predContains p t
hasFreeOccurrence (Not e) t = hasFreeOccurrence e t
hasFreeOccurrence ((:@:) v e) t 
  | v == t = False
  | otherwise = hasFreeOccurrence e t
hasFreeOccurrence ((:?:) v e) t 
  | v == t = False
  | otherwise = hasFreeOccurrence e t
hasFreeOccurrence (u :->: v) t = hasFreeOccurrence u t || hasFreeOccurrence v t  
hasFreeOccurrence (u :|: v) t = hasFreeOccurrence u t || hasFreeOccurrence v t  
hasFreeOccurrence (u :&: v) t = hasFreeOccurrence u t || hasFreeOccurrence v t 

predContains :: Pred -> Term -> Bool
predContains (Pred _) _ = False
predContains (u :=: v) t = termContains u t || termContains v t

termContains :: Term -> Term -> Bool
termContains Zero _ = False
termContains (Succ a) t = termContains a t
termContains (u :+: v) t = termContains u t || termContains v t
termContains (u :*: v) t = termContains u t || termContains v t
termContains a@(Term _) t 
  | a == t = True
  | otherwise = False

getAnnotatedExp :: Exp -> Map.Map Exp Int -> Map.Map Exp [(Exp, Int)] -> Either String AnnotatedExp
getAnnotatedExp exp mapExp mapTails = case tryAxiomSch exp of
  Right n -> Right $ AxiomSch exp $ show n
  Left axErr -> case tryAxiom exp of 
    Just m -> Right $ Axiom exp m
    Nothing -> case tryA9AxiomSch exp of 
      True -> Right $ AxiomSch exp "A9"
      False -> case tryMP exp mapExp mapTails of 
        Just annExp -> Right annExp
        Nothing -> case tryIntro exp mapExp of
          Right a -> Right a
          Left introErr -> if (introErr == isNotProved) 
            then Left axErr
            else Left introErr

tryAxiomSch :: Exp -> Either String Int
tryAxiomSch (a :->: (b :->: a')) | a == a' = Right 1 
tryAxiomSch ((a :->: b) :->: ((a' :->: (b' :->: c')) :->: (a'' :->: c''))) 
  | a == a' && a' == a'' && b == b' && c' == c'' = Right 2 
tryAxiomSch (a :->: (b :->: (a' :&: b'))) | a == a' && b == b' = Right 5
tryAxiomSch ((a :&: b) :->: a') | a == a' = Right 3
tryAxiomSch ((a :&: b) :->: b') | b == b' = Right 4
tryAxiomSch (a :->: (a' :|: b')) | a == a' = Right 6
tryAxiomSch (b :->: (a' :|: b')) | b == b' = Right 7
tryAxiomSch ((a :->: c) :->: ((b' :->: c') :->: ((a'' :|: b'') :->: c''))) 
  | a == a'' && b' == b'' && c == c' && c' == c'' = Right 8
tryAxiomSch ((a :->: b) :->: ((a' :->: (Not b')) :->: (Not a''))) | a == a' && a' == a'' && b == b' = Right 9
tryAxiomSch ((Not (Not a)) :->: a') | a == a' = Right 10

tryAxiomSch e = let
  helper :: Maybe (Maybe Term) -> Term -> Exp -> Exp -> Int -> Either String Int
  helper (Just t) x f f' n 
    | isNothing t || checkExpFree f f' x (Set.empty) (getVarsSet $ fromJust t) = Right n
    | otherwise = Left $ getAxiomErrorString x $ fromJust t 
  helper Nothing _ _ _ _ = Left isNotProved

  try11AxSch :: Exp -> Either String Int
  try11AxSch (((:@:) x f) :->: f') = helper (tryReplaceExprsVar f f' x True) x f f' 11
  try11AxSch _ = Left isNotProved

  try12AxSch :: Exp -> Either String Int
  try12AxSch (f :->: (((:?:) x f'))) = helper (tryReplaceExprsVar f' f x True) x f' f 12 
  try12AxSch _ = Left isNotProved
  in let 
    res11 = try11AxSch e
    res12 = try12AxSch e
    in if isRight res11 || isLeft res12 && res11 /= Left isNotProved
      then res11
      else res12

tryA9AxiomSch :: Exp -> Bool
tryA9AxiomSch ((f0 :&: ((:@:) x (f :->: fsucc))) :->: f') | f == f' = 
  let 
    zero = tryReplaceExprsVar f f0 x True
    succ = tryReplaceExprsVar f fsucc x True
    matches :: Maybe (Maybe Term) -> Term -> Bool
    matches Nothing _ = False
    matches (Just Nothing) _ = True
    matches (Just (Just t)) t' = t == t'
  in matches zero Zero && matches succ (Succ x)
tryA9AxiomSch _ = False

getAxiomErrorString :: Term -> Term -> String
getAxiomErrorString v t = "variable " ++ show v ++ " is not free for term " ++ show t ++ " in ?@-axiom"

getVarsSet :: Term -> Set.Set Term
getVarsSet (Succ t) = getVarsSet t
getVarsSet (t :+: t') = Set.union (getVarsSet t) (getVarsSet t')
getVarsSet (t :*: t') = Set.union (getVarsSet t) (getVarsSet t')
getVarsSet Zero = Set.empty
getVarsSet v@(Term _) = Set.singleton v

checkExpFree :: Exp -> Exp -> Term -> Set.Set Term -> Set.Set Term -> Bool
checkExpFree (Exp p) (Exp p') t quantVars termVars = checkPredFree p p' t quantVars termVars
checkExpFree (Not e) (Not e') t quantVars termVars = checkExpFree e e' t quantVars termVars
checkExpFree ((:@:) v e) ((:@:) v' e') t quantVars termVars = checkExpFree e e' t (Set.insert v quantVars) termVars
checkExpFree ((:?:) v e) ((:?:) v' e') t quantVars termVars = checkExpFree e e' t (Set.insert v quantVars) termVars
checkExpFree (u :->: v) (u' :->: v') t qV tV = checkExpFree u u' t qV tV && checkExpFree v v' t qV tV
checkExpFree (u :&: v) (u' :&: v') t qV tV = checkExpFree u u' t qV tV && checkExpFree v v' t qV tV
checkExpFree (u :|: v) (u' :|: v') t qV tV = checkExpFree u u' t qV tV && checkExpFree v v' t qV tV

checkPredFree :: Pred -> Pred -> Term -> Set.Set Term -> Set.Set Term -> Bool
checkPredFree (u :=: v) (u' :=: v') t qV tV = checkTermFree u u' t qV tV && checkTermFree v v' t qV tV
checkPredFree _ _ _ _ _ = True    

checkTermFree :: Term -> Term -> Term -> Set.Set Term -> Set.Set Term -> Bool
checkTermFree Zero Zero _ _ _ = True
checkTermFree (Succ a) (Succ a') t quantVars termVars = checkTermFree a a' t quantVars termVars
checkTermFree (a :+: b) (a' :+: b') t qV tV = checkTermFree a a' t qV tV && checkTermFree b b' t qV tV
checkTermFree (a :*: b) (a' :*: b') t qV tV = checkTermFree a a' t qV tV && checkTermFree b b' t qV tV  
checkTermFree a@(Term _) a' t quantVars termVars
  | a == t && a' /= t = (Set.member t quantVars) || (Set.null $ Set.intersection quantVars termVars)
  | otherwise = True

replaceHelper a b a' b' t isFree fun = case (fun a a' t isFree) of
  Just s -> case (fun b b' t isFree) of 
    Just s' -> if (isNothing s) 
      then Just s'
      else if (isNothing s' || s == s')
        then Just s
        else Nothing
    Nothing -> Nothing
  Nothing -> Nothing  

tryReplaceExprsVar :: Exp -> Exp -> Term -> Bool -> Maybe (Maybe Term)
tryReplaceExprsVar (Exp p) (Exp p') t isFree = tryReplacePredsVar p p' t isFree
tryReplaceExprsVar (Not e) (Not e') t isFree = tryReplaceExprsVar e e' t isFree

tryReplaceExprsVar ((:@:) v e) ((:@:) v' e') t isFree 
  | v /= v' = Nothing
  | otherwise = tryReplaceExprsVar e e' t (isFree && (v /= t))
tryReplaceExprsVar ((:?:) v e) ((:?:) v' e') t isFree
  | v /= v' = Nothing
  | otherwise = tryReplaceExprsVar e e' t (isFree && (v /= t))

tryReplaceExprsVar (a :->: b) (a' :->: b') t isFree = replaceHelper a b a' b' t isFree tryReplaceExprsVar
tryReplaceExprsVar (a :&: b) (a' :&: b') t isFree = replaceHelper a b a' b' t isFree tryReplaceExprsVar
tryReplaceExprsVar (a :|: b) (a' :|: b') t isFree = replaceHelper a b a' b' t isFree tryReplaceExprsVar
tryReplaceExprsVar _ _ _ _ = Nothing

tryReplacePredsVar :: Pred -> Pred -> Term -> Bool -> Maybe (Maybe Term)
tryReplacePredsVar (Pred p) (Pred p') _ _
  | p == p' = Just Nothing
  | otherwise = Nothing
tryReplacePredsVar (a :=: b) (a' :=: b') t isFree = replaceHelper a b a' b' t isFree tryReplaceTermsVar
tryReplacePredsVar _ _ _ _ = Nothing               

tryReplaceTermsVar :: Term -> Term -> Term -> Bool -> Maybe (Maybe Term)
tryReplaceTermsVar (Succ a) (Succ b) t isFree = tryReplaceTermsVar a b t isFree
tryReplaceTermsVar (a :+: b) (a' :+: b') t isFree = replaceHelper a b a' b' t isFree tryReplaceTermsVar
tryReplaceTermsVar (a :*: b) (a' :*: b') t isFree = replaceHelper a b a' b' t isFree tryReplaceTermsVar
tryReplaceTermsVar Zero Zero _ _ = Just Nothing
tryReplaceTermsVar a@(Term _) a' t isFree 
  | a == t && a' == t && not isFree = Just Nothing
  | a == a' && a /= t = Just Nothing
  | a == t && isFree = Just $ Just a'
  | otherwise = Nothing
tryReplaceTermsVar _ _ _ _  = Nothing

toString :: Int -> Either String AnnotatedExp -> String
toString ind (Right (AxiomSch exp n)) = "[" ++ show ind ++ ". Ax. sch. " ++ n ++ "] " ++ show exp
toString ind (Right (Axiom exp n)) = "[" ++ show ind ++ ". Ax. A" ++ show n ++ "] " ++ show exp
toString ind (Right (MP exp l k)) = "[" ++ show ind ++ ". M.P. " ++ show (l + 1) ++ ", " ++ show (k + 1) ++ "] " ++ show exp
toString ind (Right (Intro exp k)) = "[" ++ show ind ++ ". ?@-intro " ++ show (k + 1) ++ "] " ++ show exp
toString ind (Left s) 
  | s == isNotProved = "Expression " ++ show ind ++ " " ++ s ++ "." 
  | otherwise = "Expression " ++ show ind ++ ": " ++ s ++ "." 

addTail :: Exp -> Map.Map Exp [(Exp, Int)] -> Int -> Map.Map Exp [(Exp, Int)]
addTail (a :->: b) mapTails n = case Map.lookup b mapTails of
  Just xs -> Map.insert b ((a, n) : xs) mapTails
  Nothing -> Map.insert b [(a, n)] mapTails
addTail _ mapTails _ = mapTails

annotate :: [Exp] -> Exp -> [Either String AnnotatedExp]
annotate exprs provedExp = helper exprs 0 Map.empty Map.empty where
  helper :: [Exp] -> Int -> Map.Map Exp Int -> Map.Map Exp [(Exp, Int)] -> [Either String AnnotatedExp]
  helper [] _ _ _ = []
  helper (exp : es) ind mapExp mapTails = 
    let 
      annExp = getAnnotatedExp exp mapExp mapTails
    in if isLeft annExp
      then [annExp]
      else annExp : (helper es (ind + 1) (Map.insert exp ind mapExp) (addTail exp mapTails ind)) 

process :: [String] -> [String]
process input = let
  header = parse $ alexScanTokens $ head input
  Header provedExp = header
  exprs = map (getLineExp . parse . alexScanTokens) $ tail input
  annExprs = annotate exprs provedExp
  proof = (show header) : (map (uncurry toString) $ zip [1..] annExprs)
  in case last annExprs of
    Right exp -> 
      if getExp exp /= provedExp
        then proof ++ ["The proof proves different expression."]
        else proof
    Left s -> proof 

main :: IO()
main = interact (unlines . process . lines)