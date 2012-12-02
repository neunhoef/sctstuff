-- #!/usr/bin/runhaskell

{- |
Copyright   :  (c) Jeffrey Burdges 2012
License     :  GPL
Maintainer  :  Jeff Burdges (burdges at gmail dot com)
Stability   :  provisional

We provide a simple command line interface to the @simplex@ function in
@Numeric.LinearProgramming@.  

Please observe that the \# operator defined in @Numeric.LinearProgramming@ 
does not work correctly, meaning @Sparse@ equations must be given as tuples. 

Example usage :
./simplex "(Maximize [4, -3, 2]) (Sparse [ [(2,1), (1,2)] :<=: 10, [(1,2), (5,3)] :<=: 20 ]) []"

-}


{-# OPTIONS_GHC #-}
{-# LANGUAGE StandaloneDeriving #-}

{- ghc -L/usr/lib simplex.hs #-}

module Main ( main ) where

import System.Environment ( getArgs )
import Data.Char
import Numeric.LinearProgramming
import Control.Exception
import Debug.Trace

deriving instance Show Optimization
deriving instance Show Constraints

deriving instance Read t => Read (Bound t)
deriving instance Read Optimization
deriving instance Read Constraints

liftBound f (x :<=: y) = f x :<=: y
liftBound f (x :=>: y) = f x :=>: y
liftBound f (x :&: y) = f x :&: y
liftBound f (x :==: y) = f x :==: y
liftBound f (Free x) = Free (f x)

cleanup ('\\':'\n':l) = cleanup l 
cleanup (a:l) = a : (cleanup l)
cleanup [] = []

-- massageRationalStr = map (\x -> if x=='/' then '%' else x)

massageRationalStr = go 0  
  where
    go 0 (x:l) = x : go (if isDigit x then 1 else 0) l
    go 2 (x:l) = x : go (if isDigit x then 2 else 0) l
    go 1 ('/':l) = '%' : go 2 l
    go 1 ('%':l) = '%' : go 2 l
    go 1 (',':l) = '%' : '1' : ',' : go 0 l
    go 1 (' ':l) = '%' : '1' : ' ' : go 0 l
    go 1 ('\n':l) = '\n' : go 0 l
    go 1 (x:l) = x : go 1 l
    go s [] = []

do_simplex (o:b:css) = show $ simplex (read o) cs (read b)
  where
    cs = Dense $ map parse $ filter (\x -> (head x) =='[') css
    parse = liftBound (map fromRational) . read . massageRationalStr

main = interact (do_simplex . lines . cleanup)

