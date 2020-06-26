module Main where

import Lexer (alexScanTokens)
import Parser (parse)
import Types
import Proofs
import Deduction
import Annotations

import Data.Maybe (isNothing, isJust, fromJust)
import qualified Data.Set as Set
import qualified Data.Map as Map

getVarsSet :: Exp -> Set.Set Exp
getVarsSet (u :&: v) = Set.union (getVarsSet u) (getVarsSet v)
getVarsSet (u :|: v) = Set.union (getVarsSet u) (getVarsSet v)
getVarsSet (u :->: v) = Set.union (getVarsSet u) (getVarsSet v)
getVarsSet (Not e) = getVarsSet e
getVarsSet e@(Variable v) = Set.singleton e

evaluateBinary :: Exp -> Exp -> Exp -> Map.Map Exp Bool -> (Bool -> Bool -> Bool) -> Map.Map Exp Bool
evaluateBinary e u v m op = let
  m' = Map.union (evaluate u m) (evaluate v m)
  u' = m' Map.! u
  v' = m' Map.! v
  in Map.insert e (u' `op` v') m'

evaluate :: Exp -> Map.Map Exp Bool -> Map.Map Exp Bool
evaluate e@(Variable _) m = m
evaluate e@(u :&: v) m = evaluateBinary e u v m (&&)
evaluate e@(u :|: v) m = evaluateBinary e u v m (||)
evaluate e@(u :->: v) m = evaluateBinary e u v m (\u v -> not u || v) 

evaluate e@(Not u) m = let
  m' = evaluate u m
  u' = m' Map.! u
  in Map.insert e (not u') m'

generateProofBinary :: Exp -> Exp -> Exp -> Map.Map Exp Bool -> Maybe [Line]
generateProofBinary e u v m = let
  l = generateProof u m
  r = generateProof v m
  p = getProof e m
  in if isNothing l || isNothing r || isNothing p
    then Nothing 
    else Just $ fromJust l ++ fromJust r ++ fromJust p
  
generateProof :: Exp -> Map.Map Exp Bool -> Maybe [Line]
generateProof e@(u :&: v) m = generateProofBinary e u v m
generateProof e@(u :|: v) m = generateProofBinary e u v m    
generateProof e@(u :->: v) m = generateProofBinary e u v m
generateProof e@(Variable _) m = getProof e m

generateProof e@(Not (u :&: v)) m = generateProofBinary e u v m 
generateProof e@(Not (u :|: v)) m = generateProofBinary e u v m 
generateProof e@(Not (u :->: v)) m = generateProofBinary e u v m 
generateProof e@(Not (Variable _)) m = getProof e m    

generateProof e@(Not (Not u)) m = let 
  l = generateProof u m 
  p = getProof e m 
  in if isNothing l || isNothing p
    then Nothing
    else Just $ fromJust l ++ fromJust p

printContext :: [Exp] -> Exp -> String
printContext [] provedExp = " |- " ++ show provedExp
printContext (h : []) provedExp = show h ++ " |- " ++ show provedExp
printContext (h : hs) provedExp = show h ++ ", " ++ printContext hs provedExp

printResult :: [Exp] -> Exp -> [AnnotatedExp] -> [String]
printResult hyps provedExp proof = (printContext hyps provedExp) : (map (show . getExp) proof)

getExprs :: Exp -> [[Bool]] -> [Exp] -> [[Exp]] -> [([Exp], [AnnotatedExp])]
getExprs provedExp varsCombinations vars hyps = let 
    m = filter (\(_, m) -> m Map.! provedExp) $ zip hyps
      $ map (\xs -> evaluate provedExp $ Map.fromList $ zip vars xs) varsCombinations
    in map ((\(a, Just b) -> (a, annotate a b))) 
        $ filter (isJust . snd) $ map (\(hyps, m) -> (hyps, generateProof provedExp m)) m

process :: String -> [String]
process e = let 
  ProofLine provedExp = parse $ alexScanTokens e
  vars = Set.toList $ getVarsSet provedExp

  base = [False, True]
  varsCombinations = case length vars of 
    1 -> [[i] | i <- base]
    2 -> [[i, j] | (i, j) <- [(i, j) | i <- base, j <- base]]
    3 -> [[i, j, k] | (i, j, k) <- [(i, j, k) | i <- base, j <- base, k <- base]]

  helper :: (Exp, Bool) -> Exp
  helper (e, True) = e
  helper (e, False) = Not e 

  hyps = map (map helper . zip vars) varsCombinations
  fullHyps = concatMap (\e -> [e, Not e]) vars
  falseVars = map (\v -> Not v) vars
  falseProvedExp = Not provedExp 

  solve :: Exp -> [Exp] -> Maybe ([Exp], [AnnotatedExp])
  solve provedExp trueVars
    = tryReduceHypothesis (getExprs provedExp varsCombinations vars hyps) provedExp fullHyps trueVars vars (length vars)

  in case solve provedExp vars of 
    Just (h, proof) -> printResult h provedExp proof
    Nothing -> case solve falseProvedExp falseVars of 
      Just (h, proof) -> printResult h falseProvedExp proof
      Nothing -> [":("]
        
main :: IO()
main = interact (unlines . process) 

main' = do
  text <- readFile "/Users/liza/Desktop/matlog/test"
  writeFile "/Users/liza/Desktop/matlog/out" (unlines $ process text)