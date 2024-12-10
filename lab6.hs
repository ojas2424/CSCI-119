
import Data.List
import Data.Array
import Control.Monad (replicateM)
-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- Recursive reimplementation of strings function from Lab 4
strings :: Int -> [String]
strings n = concat [strs i | i <- [0..n]] where
  strs 0 = [""]
  strs n = [a:xs | a <- sigma, xs <- strs (n-1)]

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)  

type FSM a = ([a], a, [a], a -> Char -> a)


---------------- Your solution to Lab 5, ported to FSM a -------------------

-- Note: in most cases, you will need to add an Eq a => constraint
noDup :: Eq a => [a] -> Bool
noDup [] = True
noDup (x:xs) = not (elem x xs) && noDup xs

sstate :: Eq a => [a] -> [a] -> Bool
sstate [] _ = True
sstate (x:xs) ys = (elem x ys) && sstate xs ys

transition :: (Int -> Char -> Int) -> [Int] -> Bool
transition ds qs = and [elem (ds q c) qs | q <- qs, c <- sigma]

checkFSM :: FSM Int -> Bool
checkFSM (qs, s, fs, d) = (noDup qs) && (elem s qs) && (sstate fs qs) && (transition d qs)

-- Gives the delta* function (recursive in w)
dstar :: FSM Int -> Int -> [Char] -> Int
dstar m q [] = q
dstar m@(qs, s, fs, ds) q (w:ws) = 
    if (elem q qs && elem w sigma)
    then ((dstar m) (ds q w) ws) 
    else -1 

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM Int -> [Char] -> Bool
accept1 m@(qs,s,fs,ds) w = elem (dstar m s w) fs 

-- Machine acceptance, Definition 2 (via L_q(M))
accept2 :: FSM Int -> [Char] -> Bool
accept2 (qs, s, fs, d) w = aux s w where
  -- aux q w = whether the machine, starting in q, accepts w (recursive in w)
  aux :: Int -> [Char] -> Bool
  aux q [] = elem q fs
  aux q (w:ws) = aux (d q w) ws


---------------- Part 2: FSM construction

-- Define a machine that accepts exactly the strings with an odd number of b's
-- (Solution given for illustration)
oddbs :: FSM Int
oddbs = ([0,1], 0, [1], d) where
  d q 'a' = q        -- stay in the same state
  d q 'b' = 1 - q    -- switch states

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM Int
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
end_ab :: FSM Int
end_ab = ([0, 1, 2], 0, [2], d) where
	 d 0 'a' = 1
	 d 0 _   = 0
	 d 1 'b' = 2
	 d 1 'a' = 1
	 d 1 _   = 0
	 d 2 'a' = 1
	 d 2 _   = 0

exactly :: String -> FSM Int
exactly w = (qs, s, fs, d) where
    j   = length w
    qs  = [0..j+1]
    s   = 0
    fs  = [j]
    d q a  | j < q + 1      = j + 1
            | a == (w !! q)  = q + 1
            | otherwise      = j + 1
    
    

---------------- Some additional useful functions --------------------------

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Cartesian product (preserves normalization)
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Powerset  (preserves normalization)
power :: [a] -> [[a]]
power [] = [[]]
power (x:xs) = let ys = power xs
               in [] : map (x:) ys ++ tail ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys


---------------- Lab 6 begins here -----------------------------------------

-- Complete the FSM constructions for the regular expression operators
-- and test your functions adquately


-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = ([0], 0, [], d) where d 0 _ = 0

-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM i = ([0, 1, 2], 0, [1], d) where d q j = if j == i && q == 0 then 1 else 2

-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
    qs = qs1 >< qs2
    s  = (s1, s2)
    fs = [(q1, q2) | q1 <- qs1, q2<-qs2, elem q1 fs1 || elem q2 fs2] 
    d (q1, q2) a = (d1 q1 a, d2 q2 a)

-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM m1@(qs1, s1, fs1, d1) m2@(qs2, s2, fs2, d2) = (qs, s, fs, d) where
  correctX q x = if q `elem` fs1 then union x [s2] else x
  qs = [(q, correctX q x) | q <- qs1, x <- power qs2]
  s  = (s1, [s2 | s1 `elem` fs1])
  fs = [(q1,x) | (q1,x) <- qs, overlap x fs2]
  d (q,x) a = (q',x') where
     q' = d1 q a
     x' = norm $ [s2 | q' `elem` fs1] ++ map (\q2 -> d2 q2 a) x

-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = power qs1
  s  = []
  fs = [q | q <- qs, null q || overlap q fs1]
  d [] a = norm $ [s1 | q `elem` fs1] ++ [q] where q =  d1 s1 a
  d x a = norm $ [s1 | overlap x' fs1] ++ x' where
    x' = map (\q -> d1 q a) x

---------------- Bonus Features (for testing and experimenting) ------------

-- Unary set closure (where "set" = normalized list)
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, s, fs, d) = (qs', s, fs', d) where
  qs' = uclosure [s] (\q -> map (d q) sigma)
  fs' = filter (`elem` fs) qs'

-- Change the states of an FSM from an equality type to Int 
-- and use an array lookup for the transition function
intify :: Eq a => FSM a -> FSM Int
intify (qs, s, fs, d) = ([0..n-1], s', fs', d') where
  n = length qs
  m = length sigma
  s'  = ind qs s
  fs' = map (ind qs) fs
  arr = listArray ((0,0), (n-1,m-1)) [ind qs (d q a) | q <- qs, a <- sigma]
  d' q a = arr ! (q, ind sigma a)
  ind (q':qs) q = if q == q' then 0 else 1 + ind qs q

reduce :: Ord a => FSM a -> FSM Int
reduce = intify . reachable

---- Regular expressions, along with input and output
data RegExp = Empty                -- Empty language
            | Let Char             -- Single letter language
            | Union RegExp RegExp  -- Union
            | Cat RegExp RegExp    -- Concatenation
            | Star RegExp          -- Kleene star
            deriving (Show, Eq)

-- Compact display form for RegExp
newtype Compact = Compact RegExp

instance (Show Compact) where    -- use precedence to minimize parentheses
  showsPrec d (Compact r) = sp d r where
    sp d Empty         = showString "@"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star r1)     = sp 9 r1 .     -- prec(Star) = 8
                         showString "*"

-- Quick and dirty postfix RegExp parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = go w [] where
  go [] [r]              = r
  go ('+':xs) (r2:r1:rs) = go xs (Union r1 r2:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat r1 r2:rs)
  go ('*':xs) (r:rs)     = go xs (Star r:rs)
  go ('0':xs) rs         = go xs (Empty:rs)
  go ('1':xs) rs         = go xs (Star Empty:rs)
  go (x:xs) rs           = go xs (Let x:rs)

-- Use constructions above to get reduced machine associated with regex
-- Warning: it can take a lot of time/memory to compute these for "big" regex's
-- We will see much better ways later in the course
re2fsm :: RegExp -> FSM Int
re2fsm Empty = emptyFSM
re2fsm (Let c) = letterFSM c
re2fsm (Union r1 r2) = reduce $ unionFSM (re2fsm r1) (re2fsm r2)
re2fsm (Cat r1 r2) = reduce $ catFSM (re2fsm r1) (re2fsm r2)
re2fsm (Star r1) = reduce $ starFSM (re2fsm r1)
