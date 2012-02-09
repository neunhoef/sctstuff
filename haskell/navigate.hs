{-# OPTIONS_GHC -XImplicitParams #-}

import Data.List
import Data.Maybe

import qualified Data.Vector as Vec
import Data.Vector ((!), (!?), (//))

import Data.IORef

import Control.Monad
import Control.Exception

import Toolbox
import Pongo
import Necklace
import ParCosetTabel
import PubCrawl
import PCTGraph

{- --------------------- -

Usage :

nf <- loadNecklaceFileZ3 "park/kkk"
n <- init_pubcrawl nf "FEF"

stats n
ls n
graph n <index>
go n <index>
up n

counts n
finish n
failures n
tree n

 - --------------------- -}

data NeckFile pongo_t = NeckFile {
        circle :: !Int,
        necklaces :: !Necklaces,
        edgetypes :: EdgeTypes pongo_t
    }


{- Initialization -}

loadNecklaceFileZ3 :: FilePath -> IO (IORef (NeckFile Z3Pongo))
loadNecklaceFileZ3 fn = do
        (c, n, e) <- readNecklaceFileZ3 fn
        newIORef $ NeckFile { circle = c, necklaces = n, edgetypes = e }

type Navigation p = (NeckFile p,[CrawlExtend p])

init_pubcrawl :: (Pongo p) => IORef (NeckFile p) ->
               String -> IO (IORef (Navigation p))
init_pubcrawl neckfile crawl = do
        nf <- readIORef neckfile
        let ce = init_crawl_extend (circle nf) (edgetypes nf) crawl
        newIORef (nf,[ce])


{- Local -}

stats :: (Pongo p) => IORef (Navigation p) -> IO ()
stats n = do
        (_,nav) <- readIORef n
        let (f,w,m) = head nav 
        let len = length nav - 1
        putStr $ "stage " ++ show len ++ ":  "
        putStr $ "FAILs = " ++ show (length f) ++ ".  "
        putStr $ "WINs = " ++ show w ++ ".  "
        putStr $ "MOARs = " ++ show (length m) ++ ".\n"

catLines = concat . map (++ "\n")

ls :: (Pongo p) => IORef (Navigation p) -> IO ()
ls n = do
        (_,nav) <- readIORef n
        let (f,w,m) = head nav 
        putStr $ catLines $ zipWith (\i s -> show i ++ " - " ++ s) [0..]
            $ map showCrawlDepots m

failing :: (Pongo p) => IORef (Navigation p) -> IO ()
failing n = do
        (_,nav) <- readIORef n
        let (f,w,m) = head nav 
        putStr $ catLines $ zipWith (\i s -> show i ++ " - " ++ s) [0..]
            $ map showCrawlDepots f

up :: (Pongo p) => IORef (Navigation p) -> IO ()
up n = do 
        (nf,nav) <- readIORef n
        writeIORef n (nf, tail nav)

go :: (Pongo p) => IORef (Navigation p) -> Int -> IO ()
go n i = do
        (nf,nav) <- readIORef n
        let (_,_,m) = head nav 
        let crpct = m !! i
        putStrLn $ "Go : " ++ showDepots (snd crpct)
        let ce = do_crawl_extend (circle nf) (edgetypes nf) [crpct]
        writeIORef n (nf, ce:nav)

graph :: (Pongo p) => IORef (Navigation p) -> Int -> IO ()
graph n i = do
        (nf,nav) <- readIORef n
        let (_,_,m) = head nav 
        let (_,pct) = m !! i
        graph_pct pct (length nav)


{- Final -}

counts :: (Pongo p) => IORef (Navigation p) -> IO [Int]
counts n = do
        (nf,nav) <- readIORef n
        let ces = iterate_crawl_extend (circle nf) (edgetypes nf) (head nav)
        return $ map (\(a,b,c) -> length c) ces

finish :: (Pongo p) => IORef (Navigation p) -> IO ()
finish n = do
        (nf,nav) <- readIORef n
        let ces = iterate_crawl_extend (circle nf) (edgetypes nf) (head nav)
        let (f,w,m) = last ces
        putStr $ "FAILs = " ++ show (length f) ++ ".  "
        putStr $ "WINs = " ++ show w ++ ".\n"        

failures :: (Pongo p) => IORef (Navigation p) -> IO ()
failures n = do
        (_,nav) <- readIORef n
        (nf,nav) <- readIORef n
        let ces = iterate_crawl_extend (circle nf) (edgetypes nf) (head nav)
        let (f,w,m) = last ces
        putStr $ catLines $ map showCrawlDepots f

tree :: (Pongo p) => IORef (Navigation p) -> IO ()
tree n = do
        (nf,nav) <- readIORef n
        crawl_extend_tree (circle nf) (edgetypes nf) (length nav - 1) ("", head nav)


