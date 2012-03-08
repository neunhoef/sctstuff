{-# OPTIONS_GHC -XImplicitParams #-}

module Main( main ) where

import Data.List
import Data.Maybe
import qualified Data.Vector as Vec
import Data.Vector ((!), (!?), (//))
import qualified Data.ByteString.Char8 as BS

import Control.Monad
import Control.Exception
import Control.Concurrent

import Data.Rotations
import Toolbox
import Pongo
import Necklace
import ParCosetTabel
import PubCrawl
import Graphing

import System( getArgs )
import System.Console.GetOpt
import System.FilePath.Posix
import System.Exit
import System.Directory


{-  -}

allcrawls_main opts pp = do
        putStrLn ""
        exitFailure

count_by_str = map (\l -> head l ++ ":" ++ show (length l)) . group . sort

running_counter :: (Pongo p) => Int -> Options -> [CrawlExtend p] -> IO ()
running_counter k opts ces = case opt_verbosity opts of
        0 -> return ()
        1 -> putStrLn $ show $ map (length . ce_moars) ces
        2 -> putStr $ concat $ zipWith show_stage [k..] ces
  where show_stage i ce = "Stage #" ++ show i ++ ".  " ++ 
                (unwords . count_by_str . map (BS.unpack . unrotated . fst) $ ce_moars ce) ++ "\n"

saveCrawlDepots fn cd = writeFile fn $ show (length cd) ++ "\n" ++ concat ll        
  where ll = map writeCrawlDepots cd

takeParkers1 ll = ((head ll,a) : takeParkers1 b)
  where (a,b) = takeParker $ tail ll

reRotate :: BS.ByteString -> BS.ByteString -> Rotation BS.ByteString
reRotate x y = ass $ Rotate x $ fromJust i
  where i = BS.findSubstring y (BS.append x x)
        ass = assert (BS.length y == BS.length x && isJust i)

readCrawlDepots :: NeckFile p -> BS.ByteString -> [CrawlDepots p]
readCrawlDepots nf bs = let {
        f k b = Depot { idxI = k,
                 idxE = fromBS $ b !! 0,
                 idxF = fromBS $ b !! 1,
                 idxL = fromBS $ b !! 2,
                 edge_type = fromBS $ b !! 3 } ;
	wbs = wrapDepots (nf_edgetypes nf) . zipWith f [0..] ;
	fun (crawlbs,info:pctbs) = (head crawlbs, wbs pctbs) ;
	l = map fun $ takeParkers1 $ splitParker bs ;
	crawl = fst $ head l
   } in map (\(a,b) -> (reRotate crawl a,b)) l

graph_crawl_depots dn cds = let {
        fn cd k = dn ++ (pathSeparator : (BS.unpack . rotated $ fst cd)) ++ show k ;
        fun cd k = graph_pct_command (snd cd) k (fn cd k ++ ".jpg")
   } in do
          createDirectoryIfMissing False dn
          sequence_ $ zipWith fun cds [1..] 


hyphenate []     =  ""
hyphenate [w]    = w
hyphenate (w:ws) = w ++ '-' : hyphenate ws

report_filename opts c k = if (not . null $ opt_output opts)
        then opt_output opts 
        else replaceExtension (opt_neck opts) (crs ++ "." ++ c ++ show k)
  where crs = hyphenate $ opt_crawls opts 

report_results k opts ces = let {
        ce = last ces ;
        l = length ces - 1 ;
        f = ce_fails ce ;
        dump i = saveCrawlDepots fn (ce_moars $ ces !! i) 
          where fn = report_filename opts "m" (k+i)
   } in do
          sequence_ $ map dump $ opt_dump opts
          if null f then
             putStrLn $ "Success!  (mu,epsilon) = " ++ show (ce_stats ce)
          else do
             putStrLn $ "Found " ++ show (length f) ++ " failures!"
             let fn = report_filename opts "f" (k+l)
             saveCrawlDepots fn f
             if opt_graph opts then graph_crawl_depots (fn ++ ".d") f else return ()

initialized_main opts pp = do
        nf <- readNecklaceFile pp $ opt_neck opts
        let ce0 = init_crawls_extend nf $ BS.pack $ head $ opt_crawls opts
        let ces = iterate_crawl_extend nf ce0
        running_counter 0 opts ces
        report_results 0 opts ces 

resumed_main opts pp = do 
        k <- case takeExtension (opt_resume opts) of 
              '.':c:ks -> return $ read ks
              ext -> do { putStrLn $ "Unknown extension '" ++ ext ++ "', resuming blind." ; return 0; }
        bs <- BS.readFile $ opt_resume opts
        let (fn:fns) = nub . filter (not . null) $
              [ BS.unpack $ splitParker bs !! 0 !! 0, opt_neck opts ]
        if null fns then return () else
              (error $ "Neckfile " ++ head fns ++ " doesn't match " ++ fn)
        putStr $ if null (opt_crawls opts) then "" 
          else "Warning : You cannot specify crawls when resuming."
        nf <- readNecklaceFile pp fn
        exitFailure
        let ce0 = CrawlExtend {
             ce_fails = [],  ce_wins = [],  ce_stats = Nothing,
             ce_moars = readCrawlDepots nf $ BS.tail bs }
        let ces = iterate_crawl_extend nf ce0
        running_counter k opts ces
        report_results k opts ces


{- Command Line -}

data CrawlLimits = CrawlLimits {
        opt_steps	:: !Int,
        opt_time	:: !Int
    }

data Options = Options {
        opt_oops	:: IO (),
        opt_pongo	:: String,
        opt_neck	:: String,
        opt_resume	:: String,
        opt_output	:: String, 
        opt_crawls	:: [String],
        opt_dump        :: [Int],
        opt_graph	:: Bool,
        opt_verbosity	:: Int,
        opt_limits	:: CrawlLimits
    }

defaultOptions = Options {
        opt_oops	= return (),
        opt_pongo	= "",
        opt_neck	= "",
        opt_resume	= "",
        opt_dump        = [],
        opt_output	= "",
        opt_crawls	= [],
        opt_verbosity   = 1,
        opt_graph	= False,
        opt_limits = CrawlLimits { opt_steps = 0, opt_time=0 }
    }

options :: [OptDescr (Options -> Options)]
options = [
    Option "?" ["help"]
            (NoArg (\o -> o { opt_oops = do_usage } ))  
            "show version number",
    Option "v" ["version"] 
            (NoArg (\o -> o { opt_oops = do_version } ))  
            "show version number",
    Option "l" ["log"] 
            (ReqArg (\s o -> o { opt_verbosity = read s } ) "loglevel")  
            "set log level / verbosity",
    Option "n" ["neck"] 
            (ReqArg (\s o -> o { opt_neck = s }) "neckfile")  
            "Initialize new pubcrawl from necklace file",
    Option "r" ["resume"] 
            (ReqArg (\s o -> o { opt_resume = s }) "resumefile")  
            "Resume old pubcrawl",
    Option "c" ["crawl"] 
            (ReqArg (\s o -> o { opt_crawls = s : opt_crawls o }) "crawl")  
            "Resume old pubcrawl",
    Option "p" ["pongo"]
            (ReqArg (\s o -> o { opt_pongo = s }) "PONGO")
            "select optimized pongo",
    Option "g" ["graph"]  
            (NoArg (\o -> o{ opt_graph = True }))  
            "graph failed partial coset tables",
    Option "d" ["dump"] 
            (ReqArg (\s o -> o { opt_dump = read s : opt_dump o }) "dumpstep")  
            "Resume old pubcrawl"
  ]
{-
    Option "s" ["steps"] 
            (ReqArg (\s o -> o { opt_limits = opt_limits o { opt_steps = read s }) "step limit")  
            "Resume old pubcrawl",
    Option "t" ["time"] 
            (ReqArg (\s o -> o { opt_limits = opt_limits o { opt_time = read s }) "time limit")  
            "Resume old pubcrawl",
-} 


do_usage = do 
        let header = "Usage: pubcrawler [options]"
        putStrLn $ usageInfo header options
        exitSuccess

do_version = do { putStrLn "pubcrawler v0" ; exitSuccess } 

main = do
        args <- getArgs
        let ( actions, nonopts, msgs ) = getOpt Permute options args
        let opts = foldl (flip id) defaultOptions actions
        opt_oops opts
        case opt_pongo opts of
            "1"   -> main' opts parseTrivialPongo 
            "Z1"  -> main' opts parseTrivialPongo 
            "0"	  -> main' opts parseNullPongo 
            "3"	  -> main' opts parseMultZ3Pongo 
            "Z3"  -> main' opts parseMultZ3Pongo 
            _     -> error "main' parseCayleyTablePongo not yet implemented"

main' :: (Pongo p,Show p) => Options -> ParsePongo p -> IO ()
main' opts pp = m opts pp
  where m = if (not . null $ opt_resume opts) then resumed_main
            else if (null $ opt_neck opts) then (\x y -> do_usage)
            else if (null $ opt_crawls opts) then allcrawls_main
            else initialized_main


