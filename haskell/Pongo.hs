
module Pongo where

import Data.Foldable
import Data.Maybe
import qualified Data.Vector as V
import Data.Vector ((!), (!?), (//))

import qualified Data.ByteString.Char8 as BS

import Control.Exception


infixl 7 ****

class Eq p => Pongo p where 
  (****) :: p -> p -> p	{- assumed associative -}
  pzero :: p
  pone :: p
  validity :: p -> Bool
  validity = (/= pzero)
  accepting :: p -> Bool
  accepting = (== pone)
  multiply :: [p] -> Maybe p
  multiply [] = Nothing 
  multiply (x:xs) = foldl' f (Just x) xs
     where  f (Just u) v | validity w = Just w  where  w = u **** v
            f _ _ = Nothing

multipliable :: Pongo p => [p] -> Bool
multipliable [] = True
multipliable x = isJust $ multiply x

class Pongo p => InvPongo p where
  inverse :: p -> p
  pproduct :: [p] -> Maybe p
  pproduct [] = Just pone
  pproduct x = multiply x


{- Trivial Pongo used for classical small cancelation theory -}

newtype TrivialPongo = TrivialPongo () deriving (Eq, Ord, Show, Read, Bounded)
{- In theory, using newtype ... () here means it consumes no memory. -}

instance Pongo TrivialPongo where
  (****) _ _ = TrivialPongo ()
  pzero = error "pzero :: TrivialPongo cannot exist."
  pone = TrivialPongo ()
  validity _ = True
  accepting _ = True
  multiply _ = Just $ TrivialPongo ()

instance InvPongo TrivialPongo where 
  inverse _ = TrivialPongo ()
  pproduct _ = Just $ TrivialPongo ()

parseTrivialPongo :: Int -> TrivialPongo
parseTrivialPongo _ = TrivialPongo ()


{- Null Pongo that dislikes multiplication -}

data NullPongo = NPZero | NPOne  deriving (Eq, Ord, Show, Read, Bounded)

instance Pongo NullPongo where
  (****) _ _ = NPZero
  pzero = NPZero
  pone = NPOne

parseNullPongo :: Int -> NullPongo
parseNullPongo 0 = NPZero
parseNullPongo 1 = NPOne
parseNullPongo x = error $ "Null pongo has no " ++ show x ++ "."


{- Z_3 Pongo -}

data Z3Pongo = Z3One | Z3X | Z3Xinv deriving (Eq, Ord, Show, Read, Bounded)

instance Pongo Z3Pongo where
  Z3One **** x = x
  x **** Z3One = x
  Z3X **** Z3X = Z3Xinv
  Z3Xinv **** Z3Xinv = Z3X
  Z3X **** Z3Xinv = Z3One
  Z3Xinv **** Z3X = Z3One
  pzero = error "pzero :: Z3Pongo cannot exist."
  pone = Z3One
  validity _ = True

instance InvPongo Z3Pongo where 
  inverse Z3One = Z3One
  inverse Z3X = Z3Xinv
  inverse Z3Xinv = Z3X

parseMultZ3Pongo :: Int -> Z3Pongo
parseMultZ3Pongo 0 = error "Z3Pongo has no zero"
parseMultZ3Pongo 1 = Z3One
parseMultZ3Pongo 2 = Z3X
parseMultZ3Pongo 3 = Z3Xinv
parseMultZ3Pongo _ = error "Cannot employ modulo when parsing multiplicative pongos."


{- Free group generator pongo -}

data F1Pongo = F1Zero | F1One | F1X | F1Xinv deriving (Eq, Ord, Show, Read, Bounded)

instance Pongo F1Pongo where
  F1Zero **** _ = F1Zero
  _ **** F1Zero = F1Zero
  F1One **** x = x
  x **** F1One = x
  F1X **** F1Xinv = F1One
  F1Xinv **** F1X = F1One
  pzero = F1Zero
  pone = F1One

instance InvPongo F1Pongo where 
  inverse F1One = F1One
  inverse F1X = F1Xinv
  inverse F1Xinv = F1X


{- Cayley table pongo -}

data PongoCayleyTable = PongoCayleyTable {
        ct_name :: BS.ByteString,
        ct_accepting :: V.Vector Bool,
        ct_products :: V.Vector (V.Vector Int)
   } deriving (Read, Show)

instance Eq (PongoCayleyTable) where
  (==) a b = (ct_name a) == (ct_name b)

data CTPongo = CTPongo { 
        ctp_cayleytable :: PongoCayleyTable,
        ctp_index   :: !Int
   }

instance Eq (CTPongo) where
  (==) a b = assert (ctp_cayleytable a == ctp_cayleytable b) $
             ctp_index a == ctp_index b

instance Show (CTPongo) where
  show = ("CTElement" ++) . show . ctp_index

instance Pongo (CTPongo) where
  a **** b = let { ct = ctp_cayleytable a ; ctp = ct_products ct } in
             assert (ctp_cayleytable a == ctp_cayleytable b)
             CTPongo {  ctp_cayleytable = ct,
                ctp_index = ctp ! ctp_index a ! ctp_index b }
  accepting p = ct_accepting (ctp_cayleytable p) ! ctp_index p
  pzero = error "zero :: CTPongo cannot implement pzero."
  pone = error "zero :: CTPongo cannot implement pone."

parseCayleyTablePongo :: PongoCayleyTable -> Int -> CTPongo
parseCayleyTablePongo ct i = CTPongo { ctp_cayleytable = ct, ctp_index = i }


{- Group Pongo -}

{-
import Group as G

instance Group g => Pongo g where
  (****) = (G.****)
  pzero = error "zero :: GroupPongo cannot exist."
  pone = G.identify
  multiply = G.multiply
  validity _ = True

instance Group g => InvPongo g where
  inverse = G.inverse
-}



