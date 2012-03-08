
module Toolbox where

import Data.List
import Data.Maybe

import qualified Data.Vector as V
import Data.Vector ((!), (!?), (//))

import Data.Word
import Data.Bits hiding (complement)

import Control.Exception
import Debug.Trace

import Data.Rotations

{- Debuging -}

traceVal v = traceShow v v
traceFun f v = traceShow (f v) v

-- assert :: Bool -> a -> a
-- assert False x = error "Assertion failed!"
-- assert True  x = x


{- Bools -}

fromNegated :: Num a => Bool -> a
fromNegated False  = 1
fromNegated True   = 0

swap_by_sign v (a,b) 
  | v>=0 = (a,b)
  | v<0 = (b,a)
choose_by_sign v = fst . swap_by_sign v


{- Maybe -}

fixMaybes = listToMaybe . catMaybes

fixMaybe Nothing b = b
fixMaybe a b = a


{- List -}

sortUsing f = sortBy (\a b -> f a `compare` f b)
groupUsing f = groupBy (\a b -> f a == f b)
nubUsing f = nubBy (\a b -> f a == f b)

alls alphabet = [] : [ x:xs | xs <- alls alphabet, x <- alphabet ]

alls_by_len alpha = iterate pre [[]] 
  where pre l = [ x:xs | xs <- l, x <- alpha ]

divisors n = filter (\i -> n `rem` i == 0) [1..n]
proper_divisors n = takeWhile (\i -> i+i <= n) $ divisors n

powList n = concat . replicate n

sooth_crawls = map head . group . sort . map minimumRotation

allEFLcrawls = fun
  where fun = zipWith (\n -> filter (`notElem` powers n)) [1..] $
              map sooth_crawls $ iterate pre ["F"] 
        pre l = [ x:xs | xs <- l, x <- "EFL" ]
        powers n = [ powList (n `div` k) x | k <- proper_divisors n, x <- fun !! (k-1) ]

{- We eliminate crawls of the form x^n where x is another earlier crawl    -}
{- because :  If x fails, then x^m d = d with positive alcohol for some m, -}
{- and so x^{nm} = d with n times more positive alcohol.  It follows that  -}
{- powers cannot contribute to finding a crawl that never fails.           -}
{- As an aside, if x^m fails, we might still find that x dies early.       -}

clean_crawl s = and $ map ($ s) tests 
  where tests = (\s -> head s == 'F' && last s == 'L') :
                map isInfixOf ["EE","FL","LF"]

cleanEFLcrawls = map (filter clean_crawl) allEFLcrawls


{- Vector -}

indexerVector :: (t -> Int) -> V.Vector t -> Int -> [t]
indexerVector idx vec = \e -> tbl ! e
  where m = maximum $ map idx $ V.toList vec
        tbl = V.accumulate (flip (:)) (V.replicate m []) 
                 (V.map (\v -> (idx v, v)) vec)

artificizeVectorW64 :: V.Vector t -> [(Int,t)] -> (Int -> Maybe t)
artificizeVectorW64 tbl m = let {
        b :: Word64 ;
        b = foldl setBit 0 $ map ((`rem` 64) . fst) m ;
        lookup_m i = if testBit b (i `rem` 64) then lookup i m else Nothing
   } in \i -> fixMaybe (lookup_m i) (tbl !? i)


{- Partial Activities -}

data LULZ a b c = WIN a | FAIL b | MOAR c deriving (Eq, Read, Show)

isWIN (WIN _) = True
isWIN _ = False

isFAIL (FAIL _) = True
isFAIL _ = False

isMOAR (MOAR _) = True
isMOAR _ = False

wins  (WIN x:xs)  = x: wins xs
wins      (_:xs)  =    wins xs
wins           [] =    []
fails (FAIL x:xs) = x: fails xs
fails      (_:xs) =    fails xs
fails          [] =    []
moars (MOAR x:xs) = x: moars xs
moars      (_:xs) =    moars xs
moars          [] =    []



