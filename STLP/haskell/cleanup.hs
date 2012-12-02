{-# OPTIONS_GHC #-}


cleanup ('\\':'\n':l) = cleanup l 
cleanup (a:l) = a : (cleanup l)
cleanup [] = []

main = interact cleanup



