{-# OPTIONS_GHC -fspec-constr-count=30 #-}
{-# LANGUAGE ImplicitParams #-}

module PubCrawl where

import Data.List
import Data.Maybe
import qualified Data.Vector as V
import Data.Vector ((!), (!?), (//))

import Control.Monad
import Control.Exception

import Numeric.LinearProgramming
import Numeric.GSL.Root
import qualified Data.Packed.Matrix as M
import qualified Data.Packed.Vector as MV
import Numeric.LinearAlgebra.LAPACK

import Data.Rotations
import Toolbox
import Pongo
import Necklace
import ParCosetTabel

import Debug.Trace


{- Pub Crawls -}

type Crawl = Rotation (V.Vector Char)
type CrawlPerms p = Rotation [Permutation (Depot p)]

crawl_perms :: DepotsF p -> Crawl -> CrawlPerms p
crawl_perms pct = rmap $ map f . V.toList
  where f 'I' = Just
        f 'E' = mkE pct
        f 'F' = mkF pct
        f 'L' = mkL pct
--      f 'V' = mkV pct
--      f 'U' = mkU pct


type Valency p = Depot p -> Int

min_valency :: (Pongo p) => DepotsF p -> Valency p
min_valency pctf = (\(_,_,v) -> max 3 v) . consider_vertex pctf

type Drinker p = Depot p -> Int

mkdrink :: (?circle :: Int) => Valency p -> Drinker p
mkdrink valency d = curvature (edge_type d) + (?circle `div` valency d)

type CrawlCoefficients = V.Vector Int

mkdrinks :: (?circle :: Int) => Valency p -> Crawl -> CrawlCoefficients -> [Drinker p]
mkdrinks valency cr coeffs = ass $ map f $ V.toList r
  where f c = (c*) . mkdrink valency
        r = rotate coeffs (rotation cr) 
        ass = assert $ V.length coeffs == V.length (unrotated cr)


-- circle :: Int is renormilization to work with ints
-- valency :: Depot -> Int retrieves 
-- a drink is ( depot + circle / valency )
-- We ultimately divide everything by the number of drinks

data PubStat = PubStat { ps_length,ps_mu,ps_epsilon :: !Int }
       deriving (Eq,Read,Show)
type PubStep p = (Depot p,Int)
type PubCrawl p = (LULZ PubStat () (PubStep p), (Bool,V.Vector Int))

pubcrawl :: (Eq p) => [Drinker p] -> CrawlPerms p -> Depot p -> PubCrawl p
pubcrawl drinks rperms d0 = let {
        perms = rotated rperms ; 
        len_perms = length perms ; 
        dsi = cycle_partial_perms perms d0 ; 
        vsi = zipWith ($) (cycle drinks) dsi ; 
        csi = tail $ scanl (+) 0 vsi ; 
	(cs,csn) = span (>= 0) csi ; 
        stat = PubStat { 
           ps_length = length cs, 
           ps_mu = maximum $ 0:cs, 
           ps_epsilon = if null csn then 0 else head csn } ; 
	df = fst $ last $ zip dsi cs {- dsi !! i -} ;
        i = ps_length stat - 1 ; 
	step = i `rem` len_perms ; 
        b = (perms !! step) df == Nothing ; 
        b' = not $ step==0 && df==d0 ; 
        ass x = if (i<=0 || (b && b') == (b || b')) then x else err ; 
        err = error $ "PubCrawl error " ++ 
                show (stat,df /= d0,(perms !! step) df,zip dsi cs) ; 
	v = V.accum (+) (V.replicate len_perms 0) $ zip rots vs 
	    where rots = map (`rem` len_perms) [rotation rperms ..] 
	          vs = take (ps_length stat + 1) vsi ; 
   } in assert (null csn || V.sum v == ps_epsilon stat) $
        (if ps_epsilon stat < 0 then WIN stat 
         else  if b then MOAR (df,step) 
	       else {- traceShow (zip dsi csi) $ -} FAIL () ,
	 (i > 0 && not b', v) )

{- We employ the halting reason test (perms !! step) df == Nothing.         -}
{- We observe that if returning MOAR then length cs == length dsi, but   -}
{- if returning WIN then length cs < length dsi, meaning df cannot be    -}
{- dsi !! length cs in both cases.  WIN doesn't compute df, b, or step.  -}
{- Also, cycle_partial_perms and scanl each increase length by 1.        -}
{- I suppose step==0 && df == d0 might be equivalent given i>0.          -}


run_pubcrawl :: (Pongo p, ?circle :: Int) => Crawl -> CrawlCoefficients -> Depots p -> PubCrawl p
run_pubcrawl cr coeffs pct = let {
        valency = min_valency (pct !?) ;
        drinkers = mkdrinks valency cr coeffs ;
        perms = crawl_perms (pct !?) cr
   } in pubcrawl drinkers perms (pct ! 0)
       {- pub crawls start at zero. -}


{- Extend Permutation -}

artificizeVector :: V.Vector t -> [(Int,t)] -> (Int -> Maybe t)
artificizeVector tbl m = assert (length m <= 6) $
                         \i -> fixMaybe (lookup i m) (tbl !? i)

artificizeDepots :: Depots p -> [Depot p] -> DepotsF p
artificizeDepots pct = artificizeVector pct . map (\d -> (idxI d, d))

verify_extension :: (Pongo p) => Depots p -> [Depot p] -> Bool
verify_extension pct m@(x:y:_) = let {
        f = artificizeDepots pct m ; 
        -- pctm = update_depots pct m ; 
        -- f = (pctm !?) ; 
        pLf = maybeToList . mkL f ; 
        l = [x,y] ++ pLf x ++ pLf y   {- nub looks superfluous -}
   } in (and $ map (verify_face f) [x,y] ++ map (verify_vertex f) l)
        {- && (and $ map (detect_loop f) x : tail (tail m)) -}

{- We must verify_vertex for v = L y and d0/u ~ L x here, but  -}
{- w and u/d0 are covered by x and y.  See diagrams below.     -}


vector_indexer :: Int -> (t -> Int) -> V.Vector t -> Int -> [t]
vector_indexer m idx vec = \e -> tbl ! e
  where tbl = V.accumulate (flip (:)) (V.replicate (m+1) []) 
                 (V.map (\v -> (idx v, v)) vec)

-- depots_by_edgetype pct e = [d | d <- V.toList pct, e == edgetype_id (edge_type d)]
depots_by_edgetype ets = vector_indexer m (edgetype_id . edge_type)
   where m = V.maximum $ V.map edgetype_id ets

-- edgetypes_by_necklace edgetypes n = 
--          [ e | e <- V.toList edgetypes, necklace_id (necklace e) == n ] 
edgetypes_by_necklace ets = vector_indexer m (necklace_id . necklace) ets
   where m = V.maximum $ V.map (necklace_id . necklace) ets

-- depots_by_necklace pct n =
--          [ d | d <- V.toList pct, n == (necklace_id $ necklace $ edge_type d) ]
depots_by_necklace ets = vector_indexer m (necklace_id . necklace . edge_type)
   where m = V.maximum $ V.map (necklace_id . necklace) ets

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
        idxIx = V.length pct ;
        n = necklace $ edge_type z ;
        (start_bead_f,end_bead_f) = swap_by_sign psign (start_bead,end_bead) ;
        (idxF_f,idxL_f) = swap_by_sign psign (idxF,idxL) ;
        z_end_bead = end_bead_f $ edge_type z ; 
        len0 = available_length (pct !?) z ; 
        d_by_e = depots_by_edgetype edgetypes pct ; 
        d_by_n = depots_by_necklace edgetypes pct ; 
  } in assert (-1 == idxF_f z && len0 > 0) $ 
       filter (verify_extension pct) $ do
	e0 <- [ e | e <- V.toList edgetypes,  (necklace e) == n,
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
update_depots pct (x:y:ds) = (pct V.++ V.fromList [x,y]) // map (\d -> (idxI d,d)) ds


{- Linear Programming -}

conclude_linearprog :: [V.Vector Int] -> (Double,[Double])
conclude_linearprog dss = let { 
        l = V.length $ head dss ; 
        p = Minimize $ 1 : replicate l 0 ; 
        row = map fromIntegral . V.toList ; 
        cs = Dense $ ((0 : replicate l 1) :==: 1) 
                : map (\x -> (-1 : row x) :<=: 0) dss ;
        r = simplex p cs [ 1 :<=: 0 ]
    } in trace ("pubcrawl_linearprog found " ++ show r) $
         case r of 
           Optimal (epsi,epsi0:coeffs) -> (epsi,coeffs)
           Feasible (epsi,epsi0:coeffs) -> (epsi,coeffs)
           x ->  (0,[])


{- Lagrange multiplier -}

-- We minimize \sum_i f_i(x)^2 + \sum_j x_j^2 
--  subject to \sum_j x_j = 1, f_i(x)^2 ≤ 0, and x_j ≥ 0.
-- 
-- Lagrange function
--   L = \sum_i f_i(x)^2 + \sum_j x_j^2 + lambda (\sum_j x_j - 1)
-- 
-- dL/dx_j = 2 \sum_i f_i(x) df_i/dx_j(x) + 2 x_j + lambda
-- dL/dlambda = \sum_i x_i - 1
-- 
-- We know that each f_i is linear so 
-- dL^2/dx_jdx_k = 2 \sum_i df_i/dx_j(x) df_i/dx_k(x) + (j==k)
-- dL^2/dx_jdlambda = 1

inc_one j = V.imap (\i x -> if i==j then x+1 else x)

continue_lagrange :: [V.Vector Int] -> (Double,[Double])
continue_lagrange [] = (0,[])
continue_lagrange dss = let { 
        l = V.length $ head dss ; 
        dLdxj j = map (fromIntegral . (2*)) . V.toList .
                  inc_one j . foldl1' (V.zipWith (+)) $ 
                  map (\i -> V.map ((i!j) *) i) dss ; 
        m = M.fromLists $ (0: replicate l 1) : map ((1:) . dLdxj) [0 .. l-1] ; 
        b = M.asColumn $ MV.fromList (1: replicate l 0) ; 
        lambda:res = MV.toList . M.flatten $ linearSolveR m b ; 
        fi v = sum . zipWith (*) v . map fromIntegral . V.toList ; 
        epsilon = maximum $ map (fi res) dss 
   } in assert (null $ filter (/= l) $ map V.length dss) 
        (epsilon,res)

continue_lagrange' :: [V.Vector Int] -> (Double,[Double])
continue_lagrange' [] = (0,[])
continue_lagrange' dss = let { 
        l = V.length $ head dss ; 
        fi v = sum . zipWith (*) v . map fromIntegral . V.toList ; 
        fi' j i = fromIntegral $ i ! (j-1) ; 
        jL (lambda:v) 0 = sum v - 1 ; 
        jL (lambda:v) j = lambda + 
              ((2*) . sum $ map (\i -> fi v i * fi' (j-1) i) dss) ;
        zL a = map (jL a) [0..l] ;
        jkJ 0 0 = 0 ; 
        jkJ 0 _ = 1 ; 
        jkJ _ 0 = 1 ; 
        jkJ j k = (2*) $ (if j==k then 1 else 0) +
                (sum $ map (\i -> fi' j i * fi' k i) dss) ;
        zJ = [ map (jkJ j) [0..l] | j <- [0..l] ] ; 
        (_:res,_) = rootJ HybridsJ 1E-3 10 zL (\_ -> zJ) $
                     replicate (l+1) (1 / fromIntegral l) ;
        epsilon = maximum $ map (fi res) dss ;
   } in assert (null $ filter (/= l) $ map V.length dss) 
        (epsilon,res)


{- CrawlCoefficients -}

continue_coeffs :: [V.Vector Int] -> (Double,[Double]) -> CrawlCoefficients
continue_coeffs dss (epsilon,coeffs) = let {
        l = V.length $ head dss ; 
        m = maximum $  map (V.maximum . V.map abs) dss ;
        epsilon' = if epsilon >= 0 then 1 else abs epsilon ;
        d = fromIntegral (10*l) ; 
   } in V.fromList $ map (\v -> max 0 $ ceiling $ v*d) coeffs 

continue_test c dss = case (epsilon <= 0, null $ filter (<0) coeffs) of 
        (True,True) -> trace msg (epsilon, coeffs') 
        (True,False) -> trace (msg ++ "  Bad coefficients.") (0,c) 
        (False,True) -> trace (msg ++ "  Bad epsilon.") (0, c) 
        (False,False) -> trace (msg ++ "  Bad everything.") (0, c) 
  where x@(epsilon,coeffs) = continue_lagrange dss 
        coeffs' = continue_coeffs dss x 
        msg = "Changed crawl coefficients to " ++ show coeffs' ++
              " due to " ++ show (length dss) ++ " failures," ++
              " optimization yielded " ++ show coeffs ++
              " with epsilon = " ++ show epsilon ++ "."


{- Run Pub Crawl and Extend PCT -}

type CrawlDepots p = (Crawl,Depots p)

showCrawlDepots = showDepots . snd

writeDepot d = unwords $ map (show . (+1)) $
        map ($ d) [idxE, idxF, idxL, edgetype_id . edge_type]

writeCrawlDepots :: (Pongo p) => CrawlDepots p -> String
writeCrawlDepots (crawl,pct) = unlines $
        [V.toList $ rotated crawl, show $ V.length pct]
        ++ map writeDepot (V.toList pct)

sign_of_perm 'F' = 1
sign_of_perm 'L' = -1
sign_of_perm _ = error "sign_of_perm : Crawl paused off face permutation"

max_pubstats :: [PubStat] -> Maybe PubStat
max_pubstats [] = Nothing
max_pubstats (a:[]) = Just a
max_pubstats l = Just $ PubStat {
        ps_length = maximum $ map ps_length l,
        ps_mu = maximum $ map ps_mu l,
        ps_epsilon = maximum $ map ps_epsilon l }

data CrawlExtend p = CrawlExtend {
        ce_fails, ce_wins, ce_moars :: [CrawlDepots p],
        ce_stats :: Maybe PubStat,
        ce_continue :: (Double,CrawlCoefficients),
        ce_conclude :: (Double,[Double])
   }

do_crawl_extend :: (Pongo p,Show p) => NeckFile p ->
                   CrawlCoefficients -> [CrawlDepots p] -> CrawlExtend p
do_crawl_extend neckfile coeffs crpcts = let { 
        continues = map snd $ filter fst lst ;
        (res,lst) = unzip $ do 
           (crawl,pct) <- crpcts
           guard $ assert (detect_convergence pct) True
           {- guard $ trace (showDepots pct) True -}
           {- guard $ verify_pct pct -}
           guard $ assert (verify_pct pct) True
           let ?circle = nf_circle neckfile
           let (r',l) = run_pubcrawl crawl coeffs pct 
           let r = case r' of 
                    MOAR (d,step) -> do
                       let psign = sign_of_perm $ rotated crawl ! step
                       MOAR $ map ((\i -> (crawl,i)) . update_depots pct) $
                              extend_perm (nf_edgetypes neckfile) pct psign d
                    WIN x -> WIN x
                    FAIL _ -> FAIL (crawl,pct)
           return (r,l) 
   } in CrawlExtend { 
           ce_fails = fails res,
           ce_wins = [], -- wins res
           ce_stats = max_pubstats $ wins res, 
           ce_moars = concat $ moars res, 
           ce_continue = if (null $ fails res) || (null $ continues) then (-1,coeffs)
                         else continue_test coeffs continues,
           ce_conclude = if null lst then (0,[])
                         else conclude_linearprog $ map snd lst
        }

init_crawl_depots :: (Pongo p) => NeckFile p -> Crawl -> [CrawlDepots p]
init_crawl_depots neckfile crawl = do
        pct <- initialize_depots (nf_edgetypes neckfile)
        guard $ verify_pct pct
        guard $ 3*curvature (edge_type (pct ! 0)) >= -(nf_circle neckfile)
        return (crawl,pct)

init_crawls_depots :: (Pongo p) => NeckFile p -> V.Vector Char -> [CrawlDepots p]
init_crawls_depots neckfile crawl = do
        cr <- nubUsing rotated $ map (Rotate crawl) [0 .. V.length crawl - 1]
        init_crawl_depots neckfile cr

init_crawl_extend nf cr = CrawlExtend {
        ce_fails = [],  ce_wins = [],  ce_stats = Nothing,
        ce_moars = init_crawl_depots nf (Rotate cr 0),
        ce_continue = (-1, V.replicate l 1),
        ce_conclude = (0, replicate l 1) }
  where l = V.length cr

init_crawls_extend nf cr = (init_crawl_extend nf cr) 
        { ce_moars = init_crawls_depots nf cr }

next_crawl_extend' :: (Pongo p,Show p) => NeckFile p -> 
                     CrawlExtend p -> CrawlExtend p
next_crawl_extend' neckfile ce0 = let {
        -- crpcts = ce_moars ce0 ; 
        -- crawl_len = V.length $ unrotated $ fst $ head crpcts ; 
        -- coeffs = V.replicate crawl_len 1 ; 
        (_,coeffs) = ce_continue ce0 ; 
        cd0 = ce_moars ce0 ;
        ce1 = do_crawl_extend neckfile coeffs cd0 ;
        stats = max_pubstats . catMaybes $ map ce_stats [ce1,ce0]
   } in ce1 { ce_stats = stats,
           ce_fails = ce_fails ce0 ++ ce_fails ce1,
           ce_wins = ce_wins ce0 ++ ce_wins ce1 }

iterate_crawl_extend' :: (Pongo p,Show p) => NeckFile p -> 
                        CrawlExtend p -> [CrawlExtend p]
iterate_crawl_extend' neckfile ce = good ++ [all !! length good]
  where all = iterate (next_crawl_extend neckfile) ce
        good = takeWhile testsimple all
        testsimple ce' = null (ce_fails ce') && not (null $ ce_moars ce')

next_crawl_extend :: (Pongo p,Show p) => NeckFile p -> 
                     CrawlExtend p -> CrawlExtend p 
next_crawl_extend neckfile ce0 = let { 
        (_,coeffs) = ce_continue ce0 ; 
        cd0 = ce_moars ce0 ++ ce_fails ce0 ++ ce_wins ce0 ;
        ce1 = do_crawl_extend neckfile coeffs cd0 ;
        stats = max_pubstats . catMaybes $ map ce_stats [ce1,ce0]
   } in ce1 { ce_stats = stats } 

iterate_crawl_extend :: (Pongo p,Show p) => NeckFile p -> 
                        CrawlExtend p -> [CrawlExtend p]
iterate_crawl_extend neckfile ce = good ++ [all !! length good]
  where all = iterate (next_crawl_extend neckfile) ce
        good = takeWhile test all
        test ce' = (fst (ce_conclude ce') >= 0 && fst (ce_continue ce') < 0) && not (null $ ce_moars ce')

end_crawl_extend neckfile ce = (b, a, length l - 1)
  where a:b:_ = reverse l
        l = iterate_crawl_extend neckfile ce


