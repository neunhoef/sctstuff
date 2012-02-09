
module Toolbox where

import Data.List
import Data.Maybe

import qualified Data.Vector as V
import Data.Vector ((!), (!?), (//))

import Data.Word
import Data.Bits hiding (complement)

import Control.Exception
import Debug.Trace

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

rotations x =  take l . map (take l) $ tails (x++x)
  where  l = length x

minimumRotation :: Ord a => [a] -> [a]
minimumRotation = minimum . rotations

sortUsing f = sortBy (\a b -> f a `compare` f b)
groupUsing f = groupBy (\a b -> f a == f b)

swapAt n = f . splitAt n  where  f (a,b) = b++a
{- swapAt n = f . S.splitAt n  where  f (a,b) = b S.>< a -}


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



