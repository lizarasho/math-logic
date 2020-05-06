module Main where

import Lexer (alexScanTokens)
import Parser (parse)
import Types

import Data.List
import qualified Data.Set as Set
import System.IO
import Data.Maybe (isJust, fromJust, catMaybes, isNothing)
import qualified Data.Map as Map

data AnnotatedExp = Hypothesis Exp Int | Axiom Exp Int | MP Exp Int Int deriving Show
getExp :: AnnotatedExp -> Exp
getExp (Hypothesis exp _) = exp
getExp (Axiom exp _) = exp
getExp (MP exp _ _ ) = exp

checkIfHypothesis :: Exp -> [Exp] -> Maybe Int
checkIfHypothesis = elemIndex

checkIfAxiom :: Exp -> Maybe Int
checkIfAxiom (Operation Impl a (Operation Impl b a')) | a == a' = Just 1
checkIfAxiom (Operation Impl 
                  (Operation Impl a b)
                  (Operation Impl 
                        (Operation Impl a' (Operation Impl b' c'))
                        (Operation Impl a'' c''))) | a == a' && a' == a'' && b == b' && c' == c'' = Just 2 
checkIfAxiom (Operation Impl a (Operation Impl b (Operation And a' b'))) | a == a' && b == b' = Just 3
checkIfAxiom (Operation Impl (Operation And a b) a') | a == a' = Just 4
checkIfAxiom (Operation Impl (Operation And a b) b') | b == b' = Just 5
checkIfAxiom (Operation Impl a (Operation Or a' b')) | a == a' = Just 6
checkIfAxiom (Operation Impl b (Operation Or a' b')) | b == b' = Just 7
checkIfAxiom (Operation Impl 
                  (Operation Impl a c)
                  (Operation Impl 
                        (Operation Impl b' c')
                        (Operation Impl (Operation Or a'' b'') c''))) | a == a'' && b' == b'' && c' == c'' && c' == c'' = Just 8
checkIfAxiom (Operation Impl
                  (Operation Impl a b) 
                  (Operation Impl (Operation Impl a' (Not b')) (Not a''))) | a == a' && a' == a'' && b == b' = Just 9     
checkIfAxiom (Operation Impl (Not (Not a)) a') | a == a' = Just 10
checkIfAxiom _ = Nothing  
  
checkIfMP :: Exp -> Map.Map Exp Int -> Map.Map Exp [(Exp, Int)] -> Maybe AnnotatedExp
checkIfMP exp mapExp mapTails = case Map.lookup exp mapTails of
  Just xs -> case find (\(x, _) -> isJust $ Map.lookup x mapExp) xs of 
    Just (x'', v'') -> Just $ MP exp v'' $ mapExp Map.! x''
    Nothing -> Nothing
  Nothing -> Nothing 

getAnnotatedExp :: Exp -> [Exp] -> Map.Map Exp Int -> Map.Map Exp [(Exp, Int)] -> Maybe AnnotatedExp
getAnnotatedExp exp hypotheses mapExp mapTails = case checkIfHypothesis exp hypotheses of
      Just n -> Just $ Hypothesis exp $ n + 1
      Nothing -> 
        case (checkIfAxiom exp) of
          Just n ->  Just $ Axiom exp n
          Nothing -> checkIfMP exp mapExp mapTails

addTail :: Exp -> Map.Map Exp [(Exp, Int)] -> Int -> Map.Map Exp [(Exp, Int)]
addTail (Operation Impl a b) mapTails n = case Map.lookup b mapTails of
  Just xs -> Map.insert b ((a, n) : xs) mapTails
  Nothing -> Map.insert b [(a, n)] mapTails
addTail _ mapTails _ = mapTails

annotate :: [Exp] -> [Exp] -> Exp -> Maybe [AnnotatedExp]
annotate exprs hypotheses provedExp = helper exprs 0 Map.empty Map.empty where
  helper :: [Exp] -> Int -> Map.Map Exp Int -> Map.Map Exp [(Exp, Int)] -> Maybe [AnnotatedExp]
  helper [] _ _ _ = Just []
  helper (exp : es) ind mapExp mapTails = 
    let was = Map.member exp mapExp in
    case getAnnotatedExp exp hypotheses mapExp mapTails of 
      Nothing -> Nothing
      Just annExp -> 
        let res = if was 
            then helper es ind mapExp mapTails
            else helper es (ind + 1) (Map.insert exp ind mapExp) (addTail exp mapTails ind)
          in     
            case res of
              Nothing -> Nothing
              Just annExprs -> 
                if (length es == 0 && provedExp /= exp) 
                  then Nothing 
                  else if was 
                    then Just annExprs 
                    else Just (annExp : annExprs)

getMapInd :: [AnnotatedExp] -> Map.Map Int Int
getMapInd annExp = Map.fromList $ map (\(newInd, oldInd) -> (oldInd, newInd)) a where
  a = zip [0..] $ filter (`Set.member` set) [0.. length annExp - 1]
  set = Set.insert (length annExp - 1) $ getUsedIndexes annExp

getUsedIndexes :: [AnnotatedExp] -> Set.Set Int
getUsedIndexes annExp = foldr pred (Set.insert (length annExp - 1) Set.empty) (zip [0..] annExp) where
  pred (ind, (MP _ i j)) set | Set.member ind set = Set.insert i $ Set.insert j set
  pred _ set = set

toStringExp :: Int -> AnnotatedExp -> Map.Map Int Int -> String
toStringExp ind (MP exp i j) map = "[" ++ show ind ++ ". M.P. " ++ (show $ map Map.! i + 1) ++ ", " ++ (show $ map Map.! j + 1) ++ "] " ++ (show exp)
toStringExp ind (Hypothesis exp n) _ = "[" ++ show ind ++ ". Hypothesis " ++ show n ++ "] " ++ show exp
toStringExp ind (Axiom exp n) _ = "[" ++ show ind ++ ". Ax. sch. " ++ show n ++ "] " ++ show exp

filterAndRenum :: [AnnotatedExp] -> Map.Map Int Int -> [String]
filterAndRenum annExp mapInd = map (\(ind, exp) -> toStringExp (1 + mapInd Map.! ind) exp mapInd) $ filter ((`Map.member` mapInd) . fst) $ zip [0..] annExp

getInd :: Exp -> [AnnotatedExp] -> Maybe Int
getInd exp annExp = findIndex (\a -> getExp a == exp) annExp

process :: [String] -> [String]
process input = let 
  FirstLine (context, provedExp) = parse $ alexScanTokens $ head input
  exprs = map (getLineExp . parse . alexScanTokens) (tail input)
  annExprs' = annotate exprs context provedExp
  in case annExprs' of 
    Nothing -> ["Proof is incorrect"]
    Just annExprs -> 
        case (getInd provedExp annExprs) of
          Nothing -> ["Proof is incorrect"]
          Just ind ->
            (show $ FirstLine (context, provedExp)) : (filterAndRenum annExprs $ getMapInd $ take (ind + 1) annExprs)

main = interact (unlines . process . lines)  
