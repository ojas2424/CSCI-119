-- CSci 119, Lab 5
-- Reference: Lecture notes, Sections 4.1, 4.2

import Data.List (isInfixOf, isSuffixOf)  -- useful for testing in Part 2
import Data.List(nub)
-- Again, for this (and most) labs, the alphabet will be {a,b} to keep testing
-- easier, but your code should work just as well for any finite list.
sigma = ['a', 'b']

-- Finite State Machine M = (Q, s, F, d) with integer states
type FSM = ([Int], Int, [Int], Int -> Char -> Int)


---------------- Part 1: Representing FSMs

-- Check whether a finite state machine (qs, s, fs, d) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (s is in qs)
-- (3) Final states are states (fs is a subset of qs)
-- (4) Transition function d gives a state in qs for every state in qs and
--     letter from sigma
sstate :: [Int] -> [Int] -> Bool
sstate [] _ = True
sstate (x:xs) ys = (elem x ys) && sstate xs ys

transition :: (Int -> Char -> Int) -> [Int] -> Bool
transition ds qs = and [elem (ds q c) qs | q <- qs, c <- sigma]

noDup :: [Int] -> Bool
noDup [] = True
noDup (x:xs) = not (elem x xs) && noDup xs

checkFSM :: FSM -> Bool
checkFSM (qs, s, fs, d) = (noDup qs) && (elem s qs) && (sstate fs qs) && (transition d qs)

-- Gives the delta* function (recursive in w)
dstar :: FSM -> Int -> [Char] -> Int
dstar m q [] = q
dstar m@(qs, s, fs, ds) q (w:ws) = 
    if (elem q qs && elem w sigma)
    then ((dstar m) (ds q w) ws) 
    else -1 

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM -> [Char] -> Bool
accept1 m@(qs,s,fs,ds) w = elem (dstar m s w) fs 

-- Machine acceptance, Definition 2 (via L_q(M))
accept2 :: FSM -> [Char] -> Bool
accept2 (qs, s, fs, d) w = aux s w where
  -- aux q w = whether the machine, starting in q, accepts w (recursive in w)
  aux :: Int -> [Char] -> Bool
  aux q [] = elem q fs
  aux q (w:ws) = aux (d q w) ws


---------------- Part 2: FSM construction

-- Define a machine that accepts exactly the strings with an odd number of b's
-- (Solution given for illustration)
oddbs :: FSM
oddbs = ([0,1], 0, [1], d) where
  d q 'a' = q        -- stay in the same state
  d q 'b' = 1 - q    -- switch states

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM
avoid_aab = ([0,1,2,3],0,[0,1,2], f) where 
    f 3 _ = 3
    f 0 'a' = 1
    f 0 'b' = 0
    f 1 'a' = 2
    f 1 'b' = 0
    f 2 'a' = 2
    f 2 'b' = 3
    f q c = 0
	
-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM
end_ab = ([0, 1, 2], 0, [2], d) where
    d 0 'a' = 1
    d 0 _   = 0
    d 1 'b' = 2
    d 1 'a' = 1
    d 1 _   = 0
    d 2 'a' = 1
    d 2 _   = 0

-- Define a function that takes a string and returns a machine that accepts
-- exactly that string and nothing else (compare to 'onestr' from Lab 3)
-- Hint: the expression w !! i gives the i-th character of the string w
exactly :: String -> FSM
exactly w = (qs, s, fs, d) where
    j   = length w
    qs  = [0..j+1]
    s   = 0
    fs  = [j]
    d q a  | j < q + 1      = j + 1
            | a == (w !! q)  = q + 1
            | otherwise      = j + 1



-- Test the machines above. Also, try out the exerices at the end of Section 3.2
-- in my notes as FSMs. Do they produce the same results as your RegExp's did?

-- Recursive reimplementation of strings function from Lab 4
strings :: Int -> [String]
strings n = concat [strs i | i <- [0..n]] where
  strs 0 = [""]
  strs n = [a:xs | a <- sigma, xs <- strs (n-1)]

s10 = strings 10  -- or larger, if you like

-- Example test for the oddbs machine above
oddbs_test = and [accept1 oddbs w == odd (num_bs w) | w <- s10] where
  num_bs w = sum (map (\x -> if x == 'b' then 1 else 0) w)
  
