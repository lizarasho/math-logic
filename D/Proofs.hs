module Proofs where 

import Types
import Parser
import Lexer

import Data.Maybe (isNothing, fromJust)
import qualified Data.Map as Map 

replace :: Map.Map Char String -> String -> String
replace _ [] = []
replace m (c : cs)
    | Map.member c m = m Map.! c ++ replace m cs
    | otherwise = c : replace m cs

getPositiveProof :: Exp -> Exp -> Exp -> Map.Map Exp Bool -> Maybe [Line]
getPositiveProof e u v m 
    | m Map.! e = getProofBinary e (m Map.! u) (m Map.! v)
    | otherwise = getProofBinary (Not e) (m Map.! u) (m Map.! v)    

getNegateProof :: Exp -> Exp -> Exp -> Exp -> Map.Map Exp Bool -> Maybe [Line]
getNegateProof e a u v m 
    | m Map.! e = getProofBinary e (m Map.! u) (m Map.! v)
    | otherwise = let 
        l = getProof a m
        r = getProofUnary (Not e) (m Map.! a)
        in if isNothing l || isNothing r
            then Nothing  
            else Just $ fromJust l ++ fromJust r

getProof :: Exp -> Map.Map Exp Bool -> Maybe[Line]
getProof e@(u :&: v) m = getPositiveProof e u v m 
getProof e@(u :|: v) m = getPositiveProof e u v m 
getProof e@(u :->: v) m = getPositiveProof e u v m 

getProof e@(Not a@(u :&: v)) m = getNegateProof e a u v m
getProof e@(Not a@(u :|: v)) m = getNegateProof e a u v m
getProof e@(Not a@(u :->: v)) m = getNegateProof e a u v m  

getProof e@(Not (Not u)) m 
    | m Map.! u = getProofUnary e True
    | otherwise = getProofUnary (Not e) True

getProof e@(Variable v) m
    | m Map.! e = Just [ProofLine e]
    | otherwise = Just [ProofLine $ Not e]    

getProof e@(Not (Variable _)) m
    | m Map.! e = Just [ProofLine e]
    | otherwise = getProof (Not e) m

constructProof :: [(Char, String)] -> (Line -> a) -> [String] -> [a]
constructProof replacedVars f proof = 
    map (f . parse . alexScanTokens . replace (Map.fromList replacedVars)) proof    

getProofUnary :: Exp -> Bool -> Maybe[Line]
getProofUnary (Not (Not e)) True = 
    Just $ constructProof [('A', show e)] id 
    [
        "A", -- [1. Hypothesis 1]
        "(A -> (!A -> A))", -- [2. Ax. sch. 1] 
        "(!A -> A)", -- [3. M.P. 2, 1] 
        "(!A -> (!A -> !A))", -- [4. Ax. sch. 1]
        "(!A -> ((!A -> !A) -> !A))", -- [5. Ax. sch. 1] 
        "((!A -> (!A -> !A)) -> ((!A -> ((!A -> !A) -> !A)) -> (!A -> !A)))", -- [6. Ax. sch. 2] 
        "((!A -> ((!A -> !A) -> !A)) -> (!A -> !A))", -- [7. M.P. 6, 4] 
        "(!A -> !A)", -- [8. M.P. 7, 5] 
        "((!A -> A) -> ((!A -> !A) -> !!A))", -- [9. Ax. sch. 9] 
        "((!A -> !A) -> !!A)", -- [10. M.P. 9, 3] 
        "!!A" -- [11. M.P. 10, 8]
    ]
getProofUnary _ _ = Nothing    

getProofBinary :: Exp -> Bool -> Bool -> Maybe [Line]
getProofBinary (u :->: v) _ True = Just $ constructProof [('A', show u), ('B', show v)] id
    [
        "B", -- [1. Hypothesis 2]
        "(B -> (A -> B))", -- [2. Ax. sch. 1] 
        "(A -> B)" -- [3. M.P. 2, 1] 
    ]

getProofBinary (u :->: v) False _ = Just $ constructProof [('A', show u), ('B', show v)] id 
    [
        "!A", -- [1. Hypothesis 1]
        "(!A -> (!B -> !A))", -- [2. Ax. sch. 1] 
        "(!B -> !A)", -- [3. M.P. 2, 1] 
        "((!B -> !A) -> (A -> (!B -> !A)))", -- [4. Ax. sch. 1] 
        "(A -> (!B -> !A))", -- [5. M.P. 4, 3] 
        "(A -> (!B -> A))", -- [6. Ax. sch. 1]
        "((!B -> A) -> ((!B -> !A) -> !!B))", -- [7. Ax. sch. 9] 
        "(((!B -> A) -> ((!B -> !A) -> !!B)) -> (A -> ((!B -> A) -> ((!B -> !A) -> !!B))))", -- [8. Ax. sch. 1] 
        "(A -> ((!B -> A) -> ((!B -> !A) -> !!B)))", -- [9. M.P. 8, 7] 
        "((A -> (!B -> A)) -> ((A -> ((!B -> A) -> ((!B -> !A) -> !!B))) -> (A -> ((!B -> !A) -> !!B))))", -- [10. Ax. sch. 2] 
        "((A -> ((!B -> A) -> ((!B -> !A) -> !!B))) -> (A -> ((!B -> !A) -> !!B)))", -- [11. M.P. 10, 6] 
        "(A -> ((!B -> !A) -> !!B))", -- [12. M.P. 11, 9] 
        "((A -> (!B -> !A)) -> ((A -> ((!B -> !A) -> !!B)) -> (A -> !!B)))", -- [13. Ax. sch. 2] 
        "((A -> ((!B -> !A) -> !!B)) -> (A -> !!B))", -- [14. M.P. 13, 5] 
        "(A -> !!B)", -- [15. M.P. 14, 12] 
        "(!!B -> B)", -- [16. Ax. sch. 10] 
        "((!!B -> B) -> (A -> (!!B -> B)))", -- [17. Ax. sch. 1] 
        "(A -> (!!B -> B))", -- [18. M.P. 17, 16] 
        "((A -> !!B) -> ((A -> (!!B -> B)) -> (A -> B)))", -- [19. Ax. sch. 2] 
        "((A -> (!!B -> B)) -> (A -> B))", -- [20. M.P. 19, 15] 
        "(A -> B)" -- [21. M.P. 20, 18] 
    ]  
getProofBinary (Not (u :->: v)) True False = Just $ constructProof [('A', show u), ('B', show v)] id 
    [
        "A", -- [1. Hypothesis 1]
        "!B", -- [2. Hypothesis 2]
        "((A -> B) -> ((A -> B) -> (A -> B)))", -- [3. Ax. sch. 1] 
        "((A -> B) -> (((A -> B) -> (A -> B)) -> (A -> B)))", -- [4. Ax. sch. 1] 
        "(((A -> B) -> ((A -> B) -> (A -> B))) -> (((A -> B) -> (((A -> B) -> (A -> B)) -> (A -> B))) -> ((A -> B) -> (A -> B))))", -- [5. Ax. sch. 2] 
        "(((A -> B) -> (((A -> B) -> (A -> B)) -> (A -> B))) -> ((A -> B) -> (A -> B)))", -- [6. M.P. 5, 3] 
        "((A -> B) -> (A -> B))", -- [7. M.P. 6, 4] 
        "(A -> ((A -> B) -> A))", -- [8. Ax. sch. 1] 
        "((A -> B) -> A)", -- [9. M.P. 8, 1] 
        "(((A -> B) -> A) -> (((A -> B) -> (A -> B)) -> ((A -> B) -> B)))", -- [10. Ax. sch. 2] 
        "(((A -> B) -> (A -> B)) -> ((A -> B) -> B))", -- [11. M.P. 10, 9] 
        "((A -> B) -> B)", -- [12. M.P. 11, 7] 
        "(!B -> ((A -> B) -> !B))", -- [13. Ax. sch. 1] 
        "((A -> B) -> !B)", -- [14. M.P. 13, 2] 
        "(((A -> B) -> B) -> (((A -> B) -> !B) -> !(A -> B)))", -- [15. Ax. sch. 9] 
        "(((A -> B) -> !B) -> !(A -> B))", -- [16. M.P. 15, 12] 
        "!(A -> B)" -- [17. M.P. 16, 14] 
    ]       
getProofBinary (u :&: v) True True = Just $ constructProof [('A', show u), ('B', show v)] id 
    [
        "A", -- [1. Hypothesis 1]
        "B", -- [2. Hypothesis 2]
        "(A -> (B -> (A & B)))", -- [3. Ax. sch. 3] 
        "(B -> (A & B))", -- [4. M.P. 3, 1] 
        "(A & B)" -- [5. M.P. 4, 2] 
    ]
getProofBinary (Not (u :&: v)) False _ = Just $ constructProof [('A', show u), ('B', show v)] id 
    [
        "!A", -- [1. Hypothesis 1]
        "(!A -> ((A & B) -> !A))", -- [2. Ax. sch. 1] 
        "((A & B) -> !A)", -- [3. M.P. 2, 1]
        "((A & B) -> A)", -- [4. Ax. sch. 4] 
        "(((A & B) -> A) -> (((A & B) -> !A) -> !(A & B)))", -- [5. Ax. sch. 9] 
        "(((A & B) -> !A) -> !(A & B))", -- [6. M.P. 5, 4] 
        "!(A & B)" -- [7. M.P. 6, 3] 
    ]
getProofBinary (Not (u :&: v)) _ False = Just $ constructProof [('A', show u), ('B', show v)] id 
    [
        "!B", -- [1. Hypothesis 2]
        "(!B -> ((A & B) -> !B))", -- [2. Ax. sch. 1]
        "((A & B) -> !B)", -- [3. M.P. 2, 1]
        "((A & B) -> B)", -- [4. Ax. sch. 5] 
        "(((A & B) -> B) -> (((A & B) -> !B) -> !(A & B)))", -- [5. Ax. sch. 9] 
        "(((A & B) -> !B) -> !(A & B))", -- [6. M.P. 5, 4] 
        "!(A & B)" -- [7. M.P. 6, 3]
    ]
getProofBinary (u :|: v) _ True = Just $ constructProof [('A', show u), ('B', show v)] id 
    [
        "B", -- [1. Hypothesis 1]
        "(B -> (A | B))", -- [2. Ax. sch. 7] 
        "(A | B)" -- [3. M.P. 2, 1]
    ]
getProofBinary (u :|: v) True _ = Just $ constructProof [('A', show u), ('B', show v)] id 
    [
        "A", -- [1. Hypothesis 1]
        "(A -> (A | B))", -- [2. Ax. sch. 6] 
        "(A | B)" -- [3. M.P. 2, 1]
    ]    
getProofBinary (Not (u :|: v)) False False = Just $ constructProof [('A', show u), ('B', show v)] id 
    [
        "!A", -- [1. Hypothesis 1]
        "!B", -- [2. Hypothesis 2] 
        "(!A -> (!B -> (!A & !B)))", -- [3. Ax. sch. 3] 
        "(!B -> (!A & !B))", -- [4. M.P. 3, 1] 
        "(!A & !B)", -- [5. M.P. 4, 2] 
        "((!A & !B) -> ((A | B) -> (!A & !B)))", -- [6. Ax. sch. 1] 
        "((A | B) -> (!A & !B))", -- [7. M.P. 6, 5]
        "((!A & !B) -> !A)", -- [8. Ax. sch. 4] 
        "(((!A & !B) -> A) -> (((!A & !B) -> !A) -> !(!A & !B)))", -- [9. Ax. sch. 9] 
        "(A -> ((!A & !B) -> A))", -- [10. Ax. sch. 1] 
        "(((!A & !B) -> !A) -> (A -> ((!A & !B) -> !A)))", -- [11. Ax. sch. 1] 
        "(A -> ((!A & !B) -> !A))", -- [12. M.P. 11, 8] 
        "((((!A & !B) -> A) -> (((!A & !B) -> !A) -> !(!A & !B))) -> (A -> (((!A & !B) -> A) -> (((!A & !B) -> !A) -> !(!A & !B)))))", -- [13. Ax. sch. 1]
        "(A -> (((!A & !B) -> A) -> (((!A & !B) -> !A) -> !(!A & !B))))", -- [14. M.P. 13, 9] 
        "((A -> ((!A & !B) -> A)) -> ((A -> (((!A & !B) -> A) -> (((!A & !B) -> !A) -> !(!A & !B)))) -> (A -> (((!A & !B) -> !A) -> !(!A & !B)))))", -- [15. Ax. sch. 2]
        "((A -> (((!A & !B) -> A) -> (((!A & !B) -> !A) -> !(!A & !B)))) -> (A -> (((!A & !B) -> !A) -> !(!A & !B))))", -- [16. M.P. 15, 10] 
        "(A -> (((!A & !B) -> !A) -> !(!A & !B)))", -- [17. M.P. 16, 14] 
        "((A -> ((!A & !B) -> !A)) -> ((A -> (((!A & !B) -> !A) -> !(!A & !B))) -> (A -> !(!A & !B))))", -- [18. Ax. sch. 2] 
        "((A -> (((!A & !B) -> !A) -> !(!A & !B))) -> (A -> !(!A & !B)))", -- [19. M.P. 18, 12] 
        "(A -> !(!A & !B))", -- [20. M.P. 19, 17] 
        "((!A & !B) -> !B)", -- [21. Ax. sch. 5] 
        "(((!A & !B) -> B) -> (((!A & !B) -> !B) -> !(!A & !B)))", -- [22. Ax. sch. 9] 
        "(B -> ((!A & !B) -> B))", -- [23. Ax. sch. 1] 
        "(((!A & !B) -> !B) -> (B -> ((!A & !B) -> !B)))", -- [24. Ax. sch. 1] 
        "(B -> ((!A & !B) -> !B))", -- [25. M.P. 24, 21] 
        "((((!A & !B) -> B) -> (((!A & !B) -> !B) -> !(!A & !B))) -> (B -> (((!A & !B) -> B) -> (((!A & !B) -> !B) -> !(!A & !B)))))", -- [26. Ax. sch. 1] 
        "(B -> (((!A & !B) -> B) -> (((!A & !B) -> !B) -> !(!A & !B))))", -- [27. M.P. 26, 22] 
        "((B -> ((!A & !B) -> B)) -> ((B -> (((!A & !B) -> B) -> (((!A & !B) -> !B) -> !(!A & !B)))) -> (B -> (((!A & !B) -> !B) -> !(!A & !B)))))", -- [28. Ax. sch. 2] 
        "((B -> (((!A & !B) -> B) -> (((!A & !B) -> !B) -> !(!A & !B)))) -> (B -> (((!A & !B) -> !B) -> !(!A & !B))))", -- [29. M.P. 28, 23] 
        "(B -> (((!A & !B) -> !B) -> !(!A & !B)))", -- [30. M.P. 29, 27] 
        "((B -> ((!A & !B) -> !B)) -> ((B -> (((!A & !B) -> !B) -> !(!A & !B))) -> (B -> !(!A & !B))))", -- [31. Ax. sch. 2]
        "((B -> (((!A & !B) -> !B) -> !(!A & !B))) -> (B -> !(!A & !B)))", -- [32. M.P. 31, 25] 
        "(B -> !(!A & !B))", -- [33. M.P. 32, 30] 
        "((A -> !(!A & !B)) -> ((B -> !(!A & !B)) -> ((A | B) -> !(!A & !B))))", -- [34. Ax. sch. 8] 
        "((B -> !(!A & !B)) -> ((A | B) -> !(!A & !B)))", -- [35. M.P. 34, 20] 
        "((A | B) -> !(!A & !B))", -- [36. M.P. 35, 33] 
        "(((A | B) -> (!A & !B)) -> (((A | B) -> !(!A & !B)) -> !(A | B)))", -- [37. Ax. sch. 9] 
        "(((A | B) -> !(!A & !B)) -> !(A | B))", -- [38. M.P. 37, 7] 
        "!(A | B)" -- [39. M.P. 38, 36] 
    ]
getProofBinary _ _ _ = Nothing   

getImplProof :: Exp -> [Exp]
getImplProof a = constructProof [('A', show a)] getLineExp 
    [
        "(A -> (A -> A))", -- [1. Ax. sch. 1] 
        "((A -> (A -> A)) -> ((A -> ((A -> A) -> A)) -> (A -> A)))", -- [2. Ax. sch. 2] 
        "((A -> ((A -> A) -> A)) -> (A -> A))", -- [3. M.P. 2, 1] 
        "(A -> ((A -> A) -> A))", -- [4. Ax. sch. 1] 
        "(A -> A)" -- [5. M.P. 3, 4] 
    ]

getAxOrHypProof :: Exp -> Exp -> [Exp]
getAxOrHypProof a d = constructProof [('A', show a), ('D', show d)] getLineExp
    [
        "(D -> (A -> D))", -- [1. Ax. sch. 1] 
        "D", -- [2. Hypothesis 1]
        "(A -> D)" -- [3. M.P. 2, 1] 
    ]

getMPProof :: Exp -> Exp -> Exp -> [Exp]    
getMPProof a d d_ji = 
    let (d_j :->: d_i) = d_ji in 
    constructProof [('A', show a), ('I', show d_i), ('J', show d_j)] getLineExp
    [
        "(A -> J) -> (A -> J -> I) -> (A -> I)",
        "(A -> J -> I) -> (A -> I)",
        "(A -> I)"
    ]

unionProofs :: Exp -> Exp -> [Exp] -> [Exp] -> [Exp]
unionProofs a b proof proof' =
    proof ++ proof' ++ getOrProof a ++ constructProof [('A', show a), ('N', show $ Not a), ('B', show b)] getLineExp
    [
        "(A -> B) -> (N -> B) -> ((A | N) -> B)",
        "(N -> B) -> ((A | N) -> B)",
        "(A | N) -> B",
        "B"
    ]

getOrProof :: Exp -> [Exp]
getOrProof a = constructProof [('A', show a)] getLineExp $
    [
        "A -> (A | !A)"
    ] 
    ++ getContrapositionProof (Variable "A") (getLineExp $ parse $ alexScanTokens "A | !A") ++ 
    [
        "!(A | !A) -> !A",
        "!A -> (A | !A)"
    ]
    ++ getContrapositionProof (Not (Variable "A")) (getLineExp $ parse $ alexScanTokens "A | !A") ++
    [
        "!(A | !A) -> !!A",
        "(!(A | !A) -> !A) -> (!(A | !A) -> !!A) -> !!(A | !A)",
        "(!(A | !A) -> !!A) -> !!(A | !A)",
        "!!(A | !A)",
        "!!(A | !A) -> (A | !A)",
        "(A | !A)"
    ]

getContrapositionProof :: Exp -> Exp -> [String]
getContrapositionProof a b =
    map (replace (Map.fromList [('A', show a), ('B', show b)]))
    [
        "((((A -> B) -> ((A -> !B) -> !A)) -> (!B -> ((A -> B) -> ((A -> !B) -> !A)))) -> ((A -> B) -> (((A -> B) -> ((A -> !B) -> !A)) -> (!B -> ((A -> B) -> ((A -> !B) -> !A))))))", -- [1. Ax. sch. 1] 
        "(((A -> B) -> ((A -> !B) -> !A)) -> (!B -> ((A -> B) -> ((A -> !B) -> !A))))", -- [2. Ax. sch. 1] 
        "((A -> B) -> (((A -> B) -> ((A -> !B) -> !A)) -> (!B -> ((A -> B) -> ((A -> !B) -> !A)))))", -- [3. M.P. 1, 2] 
        "(((A -> B) -> ((A -> !B) -> !A)) -> ((A -> B) -> ((A -> B) -> ((A -> !B) -> !A))))", -- [4. Ax. sch. 1] 
        "((A -> B) -> ((A -> !B) -> !A))", -- [5. Ax. sch. 9] 
        "((A -> B) -> ((A -> B) -> ((A -> !B) -> !A)))", -- [6. M.P. 4, 5] 
        "(((A -> B) -> ((A -> B) -> ((A -> !B) -> !A))) -> (((A -> B) -> (((A -> B) -> ((A -> !B) -> !A)) -> (!B -> ((A -> B) -> ((A -> !B) -> !A))))) -> ((A -> B) -> (!B -> ((A -> B) -> ((A -> !B) -> !A))))))", -- [7. Ax. sch. 2] 
        "(((A -> B) -> (((A -> B) -> ((A -> !B) -> !A)) -> (!B -> ((A -> B) -> ((A -> !B) -> !A))))) -> ((A -> B) -> (!B -> ((A -> B) -> ((A -> !B) -> !A)))))", -- [8. M.P. 7, 6] 
        "((A -> B) -> (!B -> ((A -> B) -> ((A -> !B) -> !A))))", -- [9. M.P. 8, 3] 
        "((A -> B) -> (!B -> (A -> B)))", -- [10. Ax. sch. 1] 
        "(((!B -> (A -> B)) -> ((!B -> ((A -> B) -> ((A -> !B) -> !A))) -> (!B -> ((A -> !B) -> !A)))) -> ((A -> B) -> ((!B -> (A -> B)) -> ((!B -> ((A -> B) -> ((A -> !B) -> !A))) -> (!B -> ((A -> !B) -> !A))))))", -- [11. Ax. sch. 1] 
        "((!B -> (A -> B)) -> ((!B -> ((A -> B) -> ((A -> !B) -> !A))) -> (!B -> ((A -> !B) -> !A))))", -- [12. Ax. sch. 2] 
        "((A -> B) -> ((!B -> (A -> B)) -> ((!B -> ((A -> B) -> ((A -> !B) -> !A))) -> (!B -> ((A -> !B) -> !A)))))", -- [13. M.P. 11, 12] 
        "(((A -> B) -> (!B -> (A -> B))) -> (((A -> B) -> ((!B -> (A -> B)) -> ((!B -> ((A -> B) -> ((A -> !B) -> !A))) -> (!B -> ((A -> !B) -> !A))))) -> ((A -> B) -> ((!B -> ((A -> B) -> ((A -> !B) -> !A))) -> (!B -> ((A -> !B) -> !A))))))", -- [14. Ax. sch. 2] 
        "(((A -> B) -> ((!B -> (A -> B)) -> ((!B -> ((A -> B) -> ((A -> !B) -> !A))) -> (!B -> ((A -> !B) -> !A))))) -> ((A -> B) -> ((!B -> ((A -> B) -> ((A -> !B) -> !A))) -> (!B -> ((A -> !B) -> !A)))))", -- [15. M.P. 14, 10] 
        "((A -> B) -> ((!B -> ((A -> B) -> ((A -> !B) -> !A))) -> (!B -> ((A -> !B) -> !A))))", -- [16. M.P. 15, 13] 
        "(((A -> B) -> (!B -> ((A -> B) -> ((A -> !B) -> !A)))) -> (((A -> B) -> ((!B -> ((A -> B) -> ((A -> !B) -> !A))) -> (!B -> ((A -> !B) -> !A)))) -> ((A -> B) -> (!B -> ((A -> !B) -> !A)))))", -- [17. Ax. sch. 2] 
        "(((A -> B) -> ((!B -> ((A -> B) -> ((A -> !B) -> !A))) -> (!B -> ((A -> !B) -> !A)))) -> ((A -> B) -> (!B -> ((A -> !B) -> !A))))", -- [18. M.P. 17, 9] 
        "((A -> B) -> (!B -> ((A -> !B) -> !A)))", -- [19. M.P. 18, 16]
        "((!B -> (A -> !B)) -> ((A -> B) -> (!B -> (A -> !B))))", -- [20. Ax. sch. 1] 
        "(!B -> (A -> !B))", -- [21. Ax. sch. 1] 
        "((A -> B) -> (!B -> (A -> !B)))", -- [22. M.P. 20, 21] 
        "(((!B -> (A -> !B)) -> ((!B -> ((A -> !B) -> !A)) -> (!B -> !A))) -> ((A -> B) -> ((!B -> (A -> !B)) -> ((!B -> ((A -> !B) -> !A)) -> (!B -> !A)))))", -- [23. Ax. sch. 1] 
        "((!B -> (A -> !B)) -> ((!B -> ((A -> !B) -> !A)) -> (!B -> !A)))", -- [24. Ax. sch. 2] 
        "((A -> B) -> ((!B -> (A -> !B)) -> ((!B -> ((A -> !B) -> !A)) -> (!B -> !A))))", -- [25. M.P. 23, 24] 
        "(((A -> B) -> (!B -> (A -> !B))) -> (((A -> B) -> ((!B -> (A -> !B)) -> ((!B -> ((A -> !B) -> !A)) -> (!B -> !A)))) -> ((A -> B) -> ((!B -> ((A -> !B) -> !A)) -> (!B -> !A)))))", -- [26. Ax. sch. 2] 
        "(((A -> B) -> ((!B -> (A -> !B)) -> ((!B -> ((A -> !B) -> !A)) -> (!B -> !A)))) -> ((A -> B) -> ((!B -> ((A -> !B) -> !A)) -> (!B -> !A))))", -- [27. M.P. 26, 22] 
        "((A -> B) -> ((!B -> ((A -> !B) -> !A)) -> (!B -> !A)))", -- [28. M.P. 27, 25] 
        "(((A -> B) -> (!B -> ((A -> !B) -> !A))) -> (((A -> B) -> ((!B -> ((A -> !B) -> !A)) -> (!B -> !A))) -> ((A -> B) -> (!B -> !A))))", -- [29. Ax. sch. 2] 
        "(((A -> B) -> ((!B -> ((A -> !B) -> !A)) -> (!B -> !A))) -> ((A -> B) -> (!B -> !A)))", -- [30. M.P. 29, 19] 
        "((A -> B) -> (!B -> !A))" -- [31. M.P. 30, 28] 
    ]