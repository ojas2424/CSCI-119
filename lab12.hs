import Data.List (foldl')
import Data.Char (isUpper)

-- CFG G = (Start, Follows, Nullable)
type CFG = (Char, Char -> Char -> [String], Char -> Bool)

accept :: CFG -> [Char] -> Bool
accept (s,d,e) = elem [] . foldl' (\xs c -> concatMap (lq c) xs) (close [s]) where  
  close [] = [""]
  close c@(x:xs) |(isUpper x) && (e x == True) = [c] ++ close xs
                 |otherwise = [c]

bp :: CFG
bp = ('S', d, e) where
d 'S' '(' = ["S)", "S)S"]
d 'S' ')' = []
e 'S' = True ;

--{a^i b^j c^{i+j} | i >= 0, j > 0}
-- original: S --> aSc | T
--           T --> bTc | bc
-- in TNF:   S --> aSc | bTc | bc
--           T --> bTc | bc

pl = ('S', d) where
  d 'S' 'a' = ["Sc"]  ;  d 'S' 'b' = ["Tc","c"]  ;  d 'S' 'c' = []
  d 'T' 'a' = []      ;  d 'T' 'b' = ["Tc","c"]  ;  d 'T' 'c' = []

g5 :: CFG
g5 = ('S', d, e) where
    d 'S' 'a' = ["bS", "aS", "b", "aSbS", "bSaS"]; d 'S' 'b' = ["bS", "aS", "a", "aSbS", "bSaS"];  
    e 'S' = True ;

g6 :: CFG
g6 = ('S',d,e) where
    d 'S' 'a' = ["bS", "bSa", "aSba", "a", "b", "aSb", "aS", ""]; d 'S' 'b' = ["bS", "bSa", "aSba", "a", "b", "aSb", "aS", ""];
    e 'S' = True ; 
    
 
g2 :: CFG
g2 = ('R', d, e) where 
    d 'R' 'a' = ["aF", "bF", "baF", "aaF", "ba", "ab", ""] ; d 'R' 'b' = ["bF", "bR", "ba", "ab", ""] ;
    d 'F' 'a' = ["aS", "bS", ""] ; d 'F' 'b' = ["bFS", "aFS", "baFS", "aaFS", ""]
    d 'S' 'a' = ["aA", "bA", "", "abA", "bbA"] ; d 'S' 'b' = ["bS*", "aS*", "", "a", "b", "ba", "ab"] ;
    d 'A' 'a' = ["", "a", "b", "ba", "ab", "bAa", "aAa"] ;
    e 'R' = True ;