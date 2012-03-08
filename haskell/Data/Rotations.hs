
module Data.Rotations where 

import Data.List
import qualified Data.Vector as V
import qualified Data.ByteString.Char8 as BS


{- Rotatables -}

class Rotatable r where
  swapAt :: Int -> r -> r
  rotate :: r -> Int -> r
  rotations :: r -> [r]

minimumRotation :: (Ord a, Rotatable a) => a -> a
minimumRotation = minimum . rotations


{- Lists -}

instance Rotatable [a] where
  swapAt n = f . splitAt n  where  f (a,b) = b++a
  rotate x i = swapAt j x
    where l = length x
          j = i `mod` l
  rotations x =  take l . map (take l) $ tails (x++x)
    where l = length x


{- Vectors -}

instance Rotatable (V.Vector a) where 
  swapAt n = f . V.splitAt n  where  f (a,b) = b V.++ a
  rotate x = \i -> V.slice (i `mod` l) l sq
    where sq = (V.++) x x
          l = V.length x
  rotations x = map (\i -> V.slice i l sq) [0..l-1]
    where sq = (V.++) x x
          l = V.length x


{- ByteString -}

sliceBS i n x = take n $ drop i x 

instance Rotatable BS.ByteString where 
  swapAt n = f . BS.splitAt n  where  f (a,b) = BS.append b a
  rotate x = \i -> BS.take l $ BS.drop (i `mod` l) sq
    where sq = BS.append x x
          l = BS.length x
  rotations x = take l . map (BS.take l) $ BS.tails sq
    where sq = BS.append x x
          l = BS.length x


{- Rotations -}

data Rotation a = Rotate a Int  {- |  Rotations (Int -> a) Int -}

-- makeRotations :: (Rotatable r) => r -> Int -> Rotation r
-- makeRotations x k = Rotations (rotate x) k

rotation (Rotate _ k) = k
-- rotation (Rotations _ k) = k

unrotated (Rotate x _) = x
-- unrotated (Rotations f _) = f 0

rotated :: (Rotatable r) => Rotation r -> r
rotated (Rotate x k) = rotate x k
-- rotated (Rotations f k) = f k

rmap :: (a -> b) -> Rotation a -> Rotation b
rmap f (Rotate x k) = Rotate (f x) k
-- rmap f (Rotations g k) = Rotations (f . g) k

