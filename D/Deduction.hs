module Deduction where

import Data.List (sort, find)
import qualified Data.Set as Set (size, intersection, toList, (\\), isSubsetOf, fromList)
import Data.Maybe (isNothing, isJust, fromJust)

import Types
import Proofs
import Annotations

tryReduceHypothesis :: [([Exp], [AnnotatedExp])] -> Exp -> [Exp] -> [Exp] -> [Exp] -> Int -> Maybe ([Exp], [AnnotatedExp])
tryReduceHypothesis mat provedExp fullHyps vars trueVars size 
    | otherwise = let 
        result = find ((size ==) . Set.size . (Set.intersection (Set.fromList vars)) . Set.fromList . fst) mat

        matches :: Exp -> Exp -> Bool 
        matches (Not (Variable a)) (Variable b) = a /= b 
        matches (Variable a) (Not (Variable b)) = a /= b 
        matches (Variable a) (Variable b) = a /= b 
        matches _ _ = True

        helper xs = let 
            (h, proof) = head xs 
            (h', proof') = last xs 
            newHypsSet = Set.intersection (Set.fromList h) (Set.fromList h')
            a = head $ Set.toList $ (Set.fromList h) Set.\\ newHypsSet
            a' = head $ Set.toList $ (Set.fromList h') Set.\\ newHypsSet
            in union a a' provedExp (Set.toList newHypsSet) (deduce a proof) (deduce a' proof')

        hypsToUnion = case size of 
            3 -> [[[i, j, k],[i, j, Not k]] | i <- fullHyps, j <- fullHyps, k <- trueVars, i < j, matches i j, matches i k, matches j k]
            2 -> [[[i, k], [i, Not k]] | i <- fullHyps, k <- trueVars, matches i k]
            1 -> [[[i], [Not i]] | i <- trueVars]

        toUnion = filter ((== 2) . length) $ map (map fromJust) $ filter (all isJust) 
            $ map (map (\xs -> find (((sort xs) ==) . sort . fst) mat)) $ hypsToUnion 
        
        in case size of
            0 -> result
            _ -> let 
                reduced = tryReduceHypothesis (map helper toUnion) provedExp fullHyps vars trueVars (size - 1)
                in case reduced of 
                    Nothing -> result
                    _ -> reduced

union :: Exp -> Exp -> Exp -> [Exp] -> [Exp] -> [Exp] -> ([Exp], [AnnotatedExp])
union a a'@(Not _) b hyps proof proof' = (hyps, annotate hyps $ map ProofLine $ unionProofs a b (proof) (proof'))
union a'@(Not _) a b hyps proof' proof = (hyps, annotate hyps $ map ProofLine $ unionProofs a b (proof) (proof'))

deduce :: Exp -> [AnnotatedExp] -> [Exp]
deduce a proof = concatMap (prove a proof) proof

prove :: Exp -> [AnnotatedExp] -> AnnotatedExp -> [Exp]
prove a _ (AxOrHyp d)
    | d == a = getImplProof a
    | otherwise = getAxOrHypProof a d
prove a proof (MP d m n) = getMPProof a d (getExp $ proof !! n) 