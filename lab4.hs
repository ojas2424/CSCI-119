-- CSci 119, Lab 4

import Data.List (sort, stripPrefix) -- for your solution to Lab 3
import Control.Monad (replicateM) 

---------------- Code provided to you in Lab 3 ----------------

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Length-Ordered Lists over "character type" a (aka "strings")
-- Invariant: In LOL n xs, n == length xs
data LOL a = LOL Int [a] deriving (Eq,Ord)

instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is sorted with no duplicates
type Lang a = [LOL a]

-- Smart constructor for (finite) languages
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

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


---------------- Your solution to Lab 3 ----------------

-- Include here any code you need from your solution to Lab 3 for testing
-- purposes. After a few days, I will release my solution for you to use.
-- Don't duplicate the code just given above.
cart :: [a] -> [b] -> [(a,b)]
cart xs [] = []
cart [] ys = []
cart x y = [(a,b) | a <- x, b <- y]

power :: [a] -> [[a]]
power [] = [[]]
power [x] = [[], [x]]
power (x:xs) =  []: map(x:) z ++ tail z
    where 
    z = power xs 
    
dot :: LOL a -> LOL a -> LOL a
dot (LOL y ys) (LOL z zs) = LOL (y + z) (ys ++ zs)
    
rev :: LOL a -> LOL a 
rev (LOL y ys) = LOL y (reverse ys)

merge :: Ord a => Lang a -> Lang a -> Lang a
merge [] ys = ys
merge xs [] = xs 
merge (x:xs) (y:ys)
  | x < y     = x: merge xs (y:ys)
  | x == y    = x: merge xs ys
  | otherwise = y: merge (x:xs) ys

cat :: Ord a => Lang a -> Lang a -> Lang a
cat [] zs = []
cat ys [] = []
cat (y:ys) (z:zs) = dot y z : merge (cat ys (z:zs)) (cat [y] zs)

leftq :: Ord a => LOL a -> Lang a -> Lang a
leftq (LOL r ts) [] = lang []
leftq (LOL r ts) (z:zs) 
  | Nothing  == stripPrefix ts q  = leftq (LOL r ts)zs
  | otherwise = lol f: leftq (LOL r ts)zs
  where
    (LOL m q) = z 
    Just f = stripPrefix ts q

kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr 
kstar xs = eps : cat xs (kstar xs)
    
lang_of :: RegExp -> Lang Char
lang_of (Empty) = []
lang_of (Let a) = [lol[a]]
lang_of (Cat r1 r2) = cat (lang_of r1) (lang_of r2)
lang_of (Union r1 r2) = merge (lang_of r1) (lang_of r2)
lang_of (Star r1) =  kstar(lang_of r1) 

onestr :: String -> RegExp
onestr [] = Star Empty
onestr xs = if ((length xs)>1) then ((Cat (Let (head xs)) (onestr (tail xs)))) else (Let (head xs))

finite :: [String] -> RegExp
finite [] = Empty
finite [w] = onestr w
finite (w:ws) = Union (onestr w) (finite ws)



---------------- Part 1 ----------------

-- Implement the seven recursive predicates/operations on RegExp given in
-- Section 3.3 of the notes; call them empty, unitary, byp, inf, rever, lq,
-- and nep. Each should begin with a type declaration. Include several tests
-- for each function.



---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes,
-- where the second algorithm is the modified one I posted on Piazza (@96).
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "bc" =  [("","bc"), ("b","c"), ("bc","")]
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits xs = [ (take r list, drop r list) | r <- [0..length xs], list <- [xs] ]



match1 :: RegExp -> String -> Bool
match1 Empty w = False
match1 (Let a) "" = False 
match1 (Let a) (b:w) = a == b && w == []
match1 (Union r1 r2) w = (match1 r1 w) || (match1 r2 w)
match1 (Cat r1 r2) w = or [ (match1 r1 w1) && (match1 r2 w2)
                        | (w1, w2) <- (splits w) ]
match1 (Star r1) w = (w == "") || or [ w1 /= "" && (match1 r1 w1)
                  && (match1 (Star r1) w2) | (w1, w2) <- (splits w) ]


match2 :: RegExp -> String -> Bool
match2 rs w = match2' [rs] w False where
  match2' [] w c = (w=="")
  match2' (Empty:rs) w c = False
  match2' ((Let r):rs) w c = or[ match2' rs w2 False | w0 <- (splits w), w1 <- [fst w0], w1==[r], w2 <- [snd w0] ]
  match2' ((Union r1 r2):rs) w c = (match2' (r1:rs) w c) || (match2' (r2:rs) w c)
  match2' 



-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get). 

sigma = ['a', 'b']                -- Alphabet used in all examples below

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once


-- For your tests, you may also find the following helpful. For example,
-- you can generate all strings of length 10 (or 20) or less and then test
-- to see whether match1 r w == memb (lol w) (lang_of r) for each such w.

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concatMap str [0..n] where
  str 0 = [""]
  str n = [a:w | a <- sigma, w <- str (n-1)]
