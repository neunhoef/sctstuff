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
        b = (ps !! step) df == Nothing ;
        b' = not $ step==0 && df==d0 ;
        ass x = if (i<=0 || (b && b') == (b || b')) then x else err ;
        err = error ("PubCrawl error " ++ show (mu,epsilon,i,df /= d0,(ps !! step) df,zip dsi cs))
   } in if epsilon < 0 then WIN (mu, epsilon) 
        else  if b then MOAR (df,step) 
	      else {- traceShow (zip dsi csi) $ -} FAIL () 

{- We employ the halting reason test (ps !! step) df == Nothing.         -}
{- We observe that if returning MOAR then length cs == length dsi, but   -}
{- if returning WIN then length cs < length dsi, meaning df cannot be    -}
{- dsi !! length cs in both cases.  WIN doesn't compute df, b, or step.  -}
{- Also, cycle_partial_perms and scanl each increase length by 1.        -}
{- I suppose step==0 && df == d0 might be equivalent given i>0.          -}

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
        l = [x,y] ++ pLf x ++ pLf y   {- nub looks superfluous -}
   } in (and $ map (verify_face f) [x,y] ++ map (verify_vertex f) l)
        {- && (and $ map (detect_loop f) x : tail (tail m)) -}

{- We must verify_vertex for v = L y and d0/u ~ L x here, but  -}
{- w and u/d0 are covered by x and y.  See diagrams below.     -}


vector_indexer :: Int -> (t -> Int) -> Vec.Vector t -> Int -> [t]
vector_indexer m idx vec = \e -> tbl ! e
  where tbl = Vec.accumulate (flip (:)) (Vec.replicate (m+1) []) 
                 (Vec.map (\v -> (idx v, v)) vec)

-- depots_by_edgetype pct e = [d | d <- Vec.toList pct, e == edgetype_id (edge_type d)]
depots_by_edgetype ets = vector_indexer m (edgetype_id . edge_type)
   where m = Vec.maximum $ Vec.map edgetype_id ets

-- edgetypes_by_necklace edgetypes n = 
--          [ e | e <- Vec.toList edgetypes, necklace_id (necklace e) == n ] 
edgetypes_by_necklace ets = vector_indexer m (necklace_id . necklace) ets
   where m = Vec.maximum $ Vec.map (necklace_id . necklace) ets

-- depots_by_necklace pct n =
--          [ d | d <- Vec.toList pct, n == (necklace_id $ necklace $ edge_type d) ]
depots_by_necklace ets = vector_indexer m (necklace_id . necklace . edge_type)
   where m = Vec.maximum $ Vec.map (necklace_id . necklace) ets

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
{- curvature, and pongo_element in Necklace so you may az uet errors     -}

{-
 -
 - --- extend_perm visual representation ---
 -
 -        \        v/
 -     -z ?\w    y /?   -u
 -  ------  ------  ------
 -  z=b     x       u=a
 -
 -
 -        \        v/
 -     -u ?\w    y /?   -z
 -  ------  ------  ------
 -  u=b     x       z=a
 -
 - u <- -1 : [ untried depots with necklace type of d0 ]
 - v <- -1 : [ untried depots with necklace type of snd ]
 - w <- -1 : [ untried depots with necklace type of snd ]
 -  
 -}

extend_perm :: (Pongo p,Show p) => EdgeTypes p -> Depots p -> Int -> Depot p -> [[Depot p]]
extend_perm edgetypes pct psign z = let {
        idxIx = Vec.length pct ;
        n = necklace $ edge_type z ;
        (start_bead_f,end_bead_f) = swap_by_sign psign (start_bead,end_bead) ;
        (idxF_f,idxL_f) = swap_by_sign psign (idxF,idxL) ;
        z_end_bead = end_bead_f $ edge_type z ; 
        len0 = available_length (pct !?) z ; 
        d_by_e = depots_by_edgetype edgetypes pct ; 
        d_by_n = depots_by_necklace edgetypes pct ; 
  } in assert (-1 == idxF_f z && len0 > 0) $ 
       filter (verify_extension pct) $ do
	e0 <- [ e | e <- Vec.toList edgetypes,  (necklace e) == n,
	            start_bead_f e == z_end_bead,
	            length_beads e <= len0  ]
	u <- unknownDepot : [ u | 
	     u <- d_by_n (necklace_id n),  -1 == idxL_f u, 
	          u /= z,    {- digon -}
                  start_bead_f (edge_type u) == end_bead_f e0 ]
           -- u == imgE z makes xy an ok loop.
           -- u==x is monogon but impossible.
           -- u==y is degree==1 but impossible.
        let (a',b') = swap_by_sign psign (u, z)
        let x = Depot {  edge_type = e0,
                 idxI = idxIx,   idxE = idxIx + 1, 
                 idxF = idxI a', idxL = idxI b'  } 
        let a = a' { idxL = idxI x } 
        let b = b' { idxF = idxI x } 
        let e1 = complement e0 
        let n1 = necklace e1 
        let alt i j = if idxI i == idxI j then i else j
        v <- unknownDepot : 
             [ v | v' <- d_by_n (necklace_id n1),  let v = alt a v',
                 -1 == idxF v, 
                 (end_bead $ edge_type v) == start_bead e1,
                 idxI v /= idxI b,    {- F b = x /= y = F v -}
                 idxI v /= idxE a ]   {- degree==2 -}
          -- v==x is degree==1 but impossible, equivalent to u==y. 
          -- v==y is monogon but impossible. 
        w <- unknownDepot : 
             [ w | w' <- d_by_n (necklace_id n1),  let w = alt b w',
                 -1 == idxL w,
                 (start_bead $ edge_type w) == end_bead e1,
                 idxI w /= idxI v,    {- digon -}
                 idxI w /= idxI a,    {- L a = x /= y = L w -}
                 idxI w /= idxE b ]   {- degree==2 -}
          -- w==x is crazy degree==1 but impossible. 
          -- w==y is monogon but impossible.
        let len1 = sum $ map length_beads $ e0 : map edge_type [v, w]
        guard $ len1 < totallength n1
        let y = Depot {  edge_type = e1, 
                 idxI = idxIx + 1,  idxE = idxIx,
                 idxF = idxI w, idxL = idxI v  }
        let v' = v { idxF = idxI y } 
        let w' = w { idxL = idxI y } 
        return $ x : y : (nub $ filter (\i -> idxI i >= 0) [v',w',b,a])

-- let l = nub [init_depot undefined 0 1, init_depot undefined 0 2]
-- assert (length l == 1 && idxE (head l) == 1) True


update_depots :: Depots p -> [Depot p] -> Depots p
update_depots pct (x:y:ds) = (pct Vec.++ Vec.fromList [x,y]) // map (\d -> (idxI d,d)) ds


{- Run Pub Crawl and Extend PCT -}

type CrawlDepots p = (Crawl,Depots p)

showCrawlDepots = showDepots . snd

sign_of_perm 'F' = 1
sign_of_perm 'L' = -1
sign_of_perm _ = error "sign_of_perm : Crawl paused off face permutation"

max_pubstats :: [PubStat] -> Maybe PubStat
max_pubstats [] = Nothing
max_pubstats (a:[]) = Just a
max_pubstats l = Just $ f $ unzip l
  where f (x,y) = (maximum x, maximum y)

type CrawlExtend p = ([CrawlDepots p], Maybe PubStat, [CrawlDepots p])

do_crawl_extend :: (Pongo p,Show p) => Int -> EdgeTypes p ->
                   [CrawlDepots p] -> CrawlExtend p
do_crawl_extend circle edgetypes crpcts = let {
        res = do
           (crawl,pct) <- crpcts
           guard $ assert (detect_convergence pct) True
           {- guard $ detect_loops pct -}
           {- guard $ trace (showDepots pct) True -}
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

next_crawl_extend :: (Pongo p,Show p) => Int -> EdgeTypes p -> 
                     CrawlExtend p -> CrawlExtend p
next_crawl_extend circle edgetypes (b0,s0,pcts0) = (b0 ++ b1, stats, pcts1)
  where (b1,s1,pcts1) = do_crawl_extend circle edgetypes pcts0
        stats = max_pubstats $ catMaybes [s1,s0]

iterate_crawl_extend :: (Pongo p,Show p) => Int -> EdgeTypes p -> 
                        CrawlExtend p -> [CrawlExtend p]
iterate_crawl_extend circle edgetypes ce = good ++ [all !! length good]
  where all = iterate (next_crawl_extend circle edgetypes) ce
        good = takeWhile (\(b,_,m) -> null b && not (null m)) all

end_crawl_extend circle edgetypes ce = (b,a)
  where a:b:_ = reverse $ iterate_crawl_extend circle edgetypes ce


