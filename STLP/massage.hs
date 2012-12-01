{-# OPTIONS_GHC #-}

import Data.Char

massageRationalStr = go 0  
  where
    go 0 (x:l) = x : go (if isDigit x then 1 else 0) l
    go 2 (x:l) = x : go (if isDigit x then 2 else 0) l
    go 1 ('/':l) = '%' : go 2 l
    go 1 (',':l) = '%' : '1' : ',' : go 0 l
    go 1 (' ':l) = '%' : '1' : ' ' : go 0 l
    go 1 ('\n':l) = '\n' : go 0 l
    go 1 (x:l) = x : go 1 l
    go s [] = []

main = interact massageRationalStr



