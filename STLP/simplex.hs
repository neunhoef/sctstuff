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
import Numeric.LinearProgramming

deriving instance Show Optimization
deriving instance Show Constraints

deriving instance Read t => Read (Bound t)
deriving instance Read Optimization
deriving instance Read Constraints

data Simplex = Simplex Optimization Constraints Bounds deriving Read

do_simplex = show . go . read . ("Simplex " ++)
    where  go (Simplex p c b) = simplex p c b

main = do
        args <- getArgs
        if  not (null args)  
        then  putStr (unlines $ map do_simplex args)
        else  interact (unlines . map do_simplex . lines)

