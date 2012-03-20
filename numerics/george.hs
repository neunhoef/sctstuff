#!/usr/bin/perl

import Data.Bits
import Data.List
import Toolbox
import System( getArgs )
import System.Process
import System.Exit
import Debug.Trace

main = do
        args <- getArgs
        sequence_ $ map (num2pres . read) args

num2pres :: Int -> IO ExitCode
num2pres i = let {
        pongos = numZ3Pongos i ;
        (prim,pow) = find_primitive pongos ;
        len = intercalate " " $ [show prim, show pow] ;
        pg = intersperse ' ' $ take prim pongos ;
        lt = intersperse ' ' $ replicate prim '1' ;
        fn = "gg" ++ show i ;
        s = unlines . map (' ' :) $ header_lines ++ [len,pg,lt]
   } in do
          putStrLn $ unlines [ "pongos = " ++ show pongos,
              "pg = " ++ show pg, "lt = " ++ show lt ]
          writeFile (fn ++ ".pres") s
          rawSystem "./presneck" [fn ++ ".pres", fn ++ ".neck"]

header_lines = [
  "3 1",	-- <order> <accepting>
  "1 2 3",	-- cayley table of pongo
  "2 3 1",
  "3 1 2",
  "1",		-- <number of letters>
  "1",		-- inverse table of letters
  "1" ]		-- number of relators
-- relprim relpow
-- relpg[relprim]
-- rellt[relprim]

boolZ3Pongo False = '2'
boolZ3Pongo True = '3'

numZ3Pongos = map (\b -> boolZ3Pongo $ testBit b 0) . init .
              takeWhile (/=0) . iterate (\j -> shiftR j 1)

find_primitive xs = let {
        l = length xs ;
        ds = divisors l ;
        test i = let { (h,t) = splitAt i xs }
           in (concat $ replicate (l `div` i - 1) h) == t ;
        prim = head $ filter test ds ;
        pow = l `div` prim ;
   } in (prim, pow)

