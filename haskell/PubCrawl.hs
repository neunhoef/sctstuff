{-# OPTIONS_GHC -fspec-constr-count=30 #-}

module PubCrawl where

import Data.List
import Data.Maybe

import qualified Data.Vector as Vec
import Data.Vector ((!), (!?), (//))

import Control.Monad
import Control.Exception

import Toolbox
import Pongo
import Necklace
import ParCosetTabel

import Debug.Trace



{- Pub Crawl Strings -}

type Crawl = String

parse_pubcrawl :: DepotsF p -> Crawl -> [Permutation (Depot p)]
parse_pubcrawl pct = map f 
  where f 'I' = Just
        f 'E' = mkE pct
        f 'F' = mkF pct
        f 'L' = mkL pct
        f 'V' = mkV pct
        f 'U' = mkU pct
        f 'D' = error "Drink!"


{- Pub Crawl Routines -}

-- circle :: Int is renormilization to work with ints
-- valency :: Depot -> Int retrieves 
-- a drink is ( depot + circle / valency )
-- We ultimately divide everything by the number of drinks

type PubStat = (Int,Int)
type PubStep p = (Depot p,Int)
type PubCrawl p = LULZ PubStat () (PubStep p)

pubcrawl :: (Eq p) => (Depot p -> Int) -> [Permutation (Depot p)] -> Depot p -> PubCrawl p
pubcrawl drink ps d0 = let {
        dsi = cycle_partial_perms ps d0 ;
        csi = tail $ scanl (+) 0 $ map drink dsi ;
	(cs,csn) = span (>= 0) csi ;
	epsilon = if null csn then 0 else head csn ;
	mu = maximum $ 0:cs ;
        i = length cs - 1 ;
	df = dsi !! i ;
	step = i `rem` length ps ;
        b = (ps !! step) df == Nothing
   } in if epsilon < 0 then  WIN (mu, epsilon) 
        else  if b then MOAR (df,step)
	      else FAIL ()
{- We observe that if returning MOAR then length cs == length dsi, but   -}
{- if returning WIN then length cs < length dsi, meaning df cannot be    -}
{- dsi !! length cs in both cases.  WIN doesn't compute df, b, or step.  -}
{- Also, cycle_partial_perms and scanl each increase length by 1.        -}


mkdrink circle valency d = curvature (edge_type d) + (circle `div` valency d)
min_valency pctf = (\(_,_,v,_) -> max 3 v) . consider_vertex pctf

run_pubcrawl :: (Pongo p) => Int -> Crawl -> Depots p -> PubCrawl p
run_pubcrawl circle crawl pct = let {
        valency = min_valency (pct !?) ;
        drink = mkdrink circle valency ;
        ps = parse_pubcrawl (pct !?) crawl
   } in pubcrawl drink ps (pct ! 0)
       {- pub crawls start at zero. -}


{- Extend Permutation -}

artificizeVector :: Vec.Vector t -> [(Int,t)] -> (Int -> Maybe t)
artificizeVector tbl m = assert (length m <= 6) $
                         \i -> fixMaybe (lookup i m) (tbl !? i)

artificizeDepots :: Depots p -> [Depot p] -> DepotsF p
artificizeDepots pct = artificizeVector pct . map (\d -> (idxI d, d))

verify_extension :: (Pongo p) => Depots p -> [Depot p] -> Bool
verify_extension pct m@(x:y:_) = let {
        f = artificizeDepots pct m ;
        pLf = maybeToList . mkL f ;
        l = [x,y] ++ pLf x ++ pLf y ;
   } in (and $ map (verify_face f) [x,y] ++ map (verify_vertex f) l)
        {- && (and $ map (detect_loop f) x : tail (tail m)) -}

{- We must verify_vertex for v = L y and d0/u ~ L x here, -}
{- but w and u/d0 are covered by x and y.                 -}

{-
 -
 - --- extend_perm visual representation ---
 -
 -        \         v/
 -     -d0 \w    y  /   -u
 -  ------  ------  ------
 -  d0      x       u
 -
 -
 -       \         v/
 -        \w     y /   -d0
 -  ------  ------  ------
 -  u       x       d0
 -
 - u <- -1 : [ untried depots with necklace type of d0 ]
 - v <- -1 : [ untried depots with necklace type of snd ]
 - w <- -1 : [ untried depots with necklace type of snd ]
 -  
 -}

vector_indexer :: Int -> (t -> Int) -> Vec.Vector t -> Int -> [t]
vector_indexer m idx vec = \e -> tbl ! e
  where tbl = Vec.accumulate (flip (:)) (Vec.replicate (m+1) []) 
                 (Vec.map (\v -> (idx v, v)) vec)
        
-- depots_by_edgetype pct e = [d | d <- Vec.toList pct, e == edgetype_id (edge_type d)]
depots_by_edgetype ets = vector_indexer m (edgetype_id . edge_type)
   where m = maximum $ map edgetype_id $ Vec.toList ets

-- edgetypes_by_necklace edgetypes n = 
--          [ e | e <- Vec.toList edgetypes, necklace_id (necklace e) == n ] 
edgetypes_by_necklace ets = vector_indexer m (necklace_id . necklace) ets
   where m = maximum $ map (necklace_id . necklace) $ Vec.toList ets

-- depots_by_necklace pct n =
--          [ d | d <- Vec.toList pct, n == (necklace_id $ necklace $ edge_type d) ]
depots_by_necklace ets = vector_indexer m (necklace_id . necklace . edge_type)
   where m = maximum $ map (necklace_id . necklace) $ Vec.toList ets

unknownEdgeType = let {
        uet s = error $ "Accessing unknownEdgeType's " ++ s ;
        n = Necklace { necklace_id = -1, primlen = 0, power = 0,
               necklace_name = uet "necklace_name" } 
   } in EdgeType {
        edgetype_id = -1,
        complement = uet "complement", 
        necklace = n,
        start_bead = 0,		{- uet "start_bead" -}
        length_beads = 1, 
        curvature = 0,		{- uet "curvature" -}
        pongo_element = uet "pongo_element" }
unknownDepot = init_depot unknownEdgeType (-1) (-1)
{- You can debug this by removing the strictness flags on start_bead and  -}
{- curvature, and pongo_element in Necklace so you may add uet errors     -}

extend_perm :: (Pongo p) => EdgeTypes p -> Depots p -> Int -> Depot p -> [[Depot p]]
extend_perm edgetypes pct psign dd = let {
        idxI0 = Vec.length pct ;
        n = necklace $ edge_type dd ;
        (start_bead_f,end_bead_f) = swap_by_sign psign (start_bead,end_bead) ;
        (idxF_f,idxL_f) = swap_by_sign psign (idxF,idxL) ;
        dd_bead = end_bead_f $ edge_type dd ;
        len0 = available_length (pct !?) dd ;
        d_by_e = depots_by_edgetype edgetypes pct ;
        d_by_n = depots_by_necklace edgetypes pct ;
        e0s = [ e | e <- Vec.toList edgetypes,  (necklace e) == n ]
  } in assert (-1 == idxF_f dd) $
       filter (verify_extension pct) $ do
	e0 <- [ e | e <- e0s, start_bead_f e == dd_bead, 
	            length_beads e <= len0 ]
	eu <- [ e | e <- e0s, start_bead_f e == end_bead_f e0,
	            length_beads e + length_beads e0 <= len0 ]
        u  <- init_depot eu (-1) (-1) : 
              [ d | d <- d_by_e (edgetype_id eu), 
                    -1 == idxL_f d,
                    d /= dd, idxI d /= idxE dd, 
                    idxI d /= idxI0, idxI d /= idxI0+1 ]
        let e1 = complement e0 
        let n1 = necklace e1 
        v  <- unknownDepot : 
              [ d | d <- d_by_n (necklace_id n1),  -1 == idxF d, 
                    (end_bead $ edge_type d) == start_bead e1, 
                    idxI d /= idxI dd, idxI d /= idxE dd, 
                    idxI d /= idxI0, idxI d /= idxI0+1, 
                    idxI d /= idxI u ]
        w  <- unknownDepot : 
              [ d | d <- d_by_n (necklace_id n1),  -1 == idxL d,
                    (start_bead $ edge_type d) == end_bead e1,
                    d /= dd, idxI d /= idxE dd, 
                    idxI d /= idxI0, idxI d /= idxI0+1, 
                    idxI d /= idxI u, idxI d /= idxI v ]
        let len1 = sum $ map length_beads $ e0 : map edge_type [v, w]
        guard $ len1 < totallength n1
        let (a,b) = swap_by_sign psign (u, dd)
        let x = Depot {  edge_type = e0,
                 idxI = idxI0,  idxE = idxI0 + 1, 
                 idxF = idxI a, idxL = idxI b  } 
        let y = Depot {  edge_type = e1, 
                 idxI = idxI0 + 1,  idxE = idxI0,
                 idxF = idxI w, idxL = idxI v  }
        return $ filter (\i -> idxI i >= 0) [ x,y, 
          a { idxL = idxI x }, b { idxF = idxI x },
          w { idxL = idxI y }, v { idxF = idxI y } ]

update_depots :: Depots p -> [Depot p] -> Depots p
update_depots pct (x:y:ds) = (pct Vec.++ Vec.fromList [x,y]) // map (\d -> (idxI d,d)) ds


{- Run Pub Crawl and Extend PCT -}

type CrawlDepots p = (Crawl,Depots p)

showCrawlDepots = showDepots . snd

sign_of_perm 'F' = 1
sign_of_perm 'L' = -1
sign_of_perm _ = error "Crawl paused off face permutation"

max_pubstats :: [PubStat] -> Maybe PubStat
max_pubstats [] = Nothing
max_pubstats (a:[]) = Just a
max_pubstats l = Just $ f $ unzip l
  where f (x,y) = (maximum x, maximum y)

type CrawlExtend p = ([CrawlDepots p], Maybe PubStat, [CrawlDepots p])

do_crawl_extend :: (Pongo p) => Int -> EdgeTypes p ->
                   [CrawlDepots p] -> CrawlExtend p
do_crawl_extend circle edgetypes crpcts = let {
        res = do
           (crawl,pct) <- crpcts
           {- guard $ detect_loops pct -}
           guard $ verify_pct pct
           case run_pubcrawl circle crawl pct of
              MOAR (d,step) -> do
                 let psign = sign_of_perm $ crawl !! step
                 let lds = extend_perm edgetypes pct psign d
                 map (MOAR . (\i -> (crawl,i)) . update_depots pct) lds
              WIN x -> return $ WIN x
              FAIL _ -> return $ FAIL (crawl,pct)
   } in (fails res, max_pubstats $ wins res, moars res)

init_crawl_depots :: Int -> EdgeTypes p -> Crawl -> [CrawlDepots p]
init_crawl_depots circle edgetypes crawl = do
        pct <- initialize_depots edgetypes
        guard $ 3*curvature (edge_type (pct ! 0)) >= -circle
        return (crawl,pct)

init_crawls_depots :: Int -> EdgeTypes p -> Crawl -> [CrawlDepots p]
init_crawls_depots circle edgetypes crawl = do
        cr <- nub $ rotations crawl
        init_crawl_depots circle edgetypes cr
        {- add filter (\s -> head s == 'D')  -}

init_crawl_extend circle et cr = ([], Nothing, init_crawl_depots circle et cr)
init_crawls_extend circle et cr = ([], Nothing, init_crawls_depots circle et cr)

next_crawl_extend :: (Pongo p) => Int -> EdgeTypes p -> 
                     CrawlExtend p -> CrawlExtend p
next_crawl_extend circle edgetypes (b0,s0,pcts0) = (b0 ++ b1, stats, pcts1)
  where (b1,s1,pcts1) = do_crawl_extend circle edgetypes pcts0
        stats = max_pubstats $ catMaybes [s1,s0]

iterate_crawl_extend :: (Pongo p) => Int -> EdgeTypes p -> 
                        CrawlExtend p -> [CrawlExtend p]
iterate_crawl_extend circle edgetypes ce = good ++ [all !! length good]
  where all = iterate (next_crawl_extend circle edgetypes) ce
        good = takeWhile (\(b,_,m) -> null b && not (null m)) all

end_crawl_extend circle edgetypes ce = (b,a)
  where a:b:_ = reverse $ iterate_crawl_extend circle edgetypes ce


