module Annotations where

import Types

import Data.Maybe (isJust, fromJust)
import Data.List (find)
import qualified Data.Map as Map

tryAxiomSch :: Exp -> Bool
tryAxiomSch (a :->: (b :->: a')) | a == a' = True
tryAxiomSch ((a :->: b) :->: ((a' :->: (b' :->: c')) :->: (a'' :->: c''))) 
        | a == a' && a' == a'' && b == b' && c' == c'' = True
tryAxiomSch (a :->: (b :->: (a' :&: b'))) | a == a' && b == b' = True
tryAxiomSch ((a :&: b) :->: a') | a == a' = True
tryAxiomSch ((a :&: b) :->: b') | b == b' = True
tryAxiomSch (a :->: (a' :|: b')) | a == a' = True
tryAxiomSch (b :->: (a' :|: b')) | b == b' = True
tryAxiomSch ((a :->: c) :->: ((b' :->: c') :->: ((a'' :|: b'') :->: c''))) 
        | a == a'' && b' == b'' && c == c' && c' == c'' = True
tryAxiomSch ((a :->: b) :->: ((a' :->: (Not b')) :->: (Not a''))) | a == a' && a' == a'' && b == b' = True
tryAxiomSch ((Not (Not a)) :->: a') | a == a' = True
tryAxiomSch _ = False

tryMP :: Exp -> Map.Map Exp Int -> Map.Map Exp [(Exp, Int)] -> Maybe (Int, Int)
tryMP exp mapExp mapTails = case Map.lookup exp mapTails of
  Just xs -> case find (\(x, _) -> isJust $ Map.lookup x mapExp) xs of 
    Just (x'', v'') -> Just $ (mapExp Map.! x'', v'')
    Nothing -> Nothing
  Nothing -> Nothing 

tryHypothesis :: Exp -> [Exp] -> Bool
tryHypothesis = elem

getAnnotatedExp :: Exp -> [Exp] -> Map.Map Exp Int -> Map.Map Exp [(Exp, Int)] -> AnnotatedExp
getAnnotatedExp exp hypotheses mapExp mapTails = case tryAxiomSch exp || tryHypothesis exp hypotheses of 
  True -> AxOrHyp exp 
  False -> uncurry (MP exp) (fromJust $ tryMP exp mapExp mapTails)

addTail :: Exp -> Map.Map Exp [(Exp, Int)] -> Int -> Map.Map Exp [(Exp, Int)]
addTail (a :->: b) mapTails n = case Map.lookup b mapTails of
  Just xs -> Map.insert b ((a, n) : xs) mapTails
  Nothing -> Map.insert b [(a, n)] mapTails
addTail _ mapTails _ = mapTails    

annotate :: [Exp] -> [Line] -> [AnnotatedExp]
annotate hypotheses exprs = helper (map getLineExp exprs) 0 Map.empty Map.empty where
  helper :: [Exp] -> Int -> Map.Map Exp Int -> Map.Map Exp [(Exp, Int)] -> [AnnotatedExp]
  helper [] _ _ _ = []
  helper (exp : es) ind mapExp mapTails = 
    (getAnnotatedExp exp hypotheses mapExp mapTails) 
      : (helper es (ind + 1) (Map.insert exp ind mapExp) (addTail exp mapTails ind))  