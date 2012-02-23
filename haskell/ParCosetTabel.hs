{-# OPTIONS_GHC -XStandaloneDeriving -XTypeSynonymInstances -XFlexibleInstances -XBangPatterns #-}

module ParCosetTabel where 

import Data.List
import Data.Maybe
import qualified Data.Bits as Bits
import qualified Data.Vector as V
import Data.Vector ((!), (!?), (//))

import Control.Monad
import Control.Exception

import Toolbox
import Pongo
import Necklace

import Debug.Trace

{- Depots / Partial Coset Table -}

data DepotE edge_type_t = Depot {
       edge_type :: edge_type_t,
       idxI, idxE, idxF, idxL :: !Int
    } 
instance Eq (DepotE t) where
  (==) a b = idxI a == idxI b

type Depot pongo_t = DepotE (EdgeType pongo_t)

type Depots pongo_t = V.Vector (Depot pongo_t)
type DepotsF pongo_t = Int -> Maybe (Depot pongo_t)


{- Read Partial Coset Tables -}

type DepotIO = DepotE Int

wrapDepot :: EdgeTypes p -> DepotIO -> Depot p
wrapDepot edgetypes d = d { edge_type = edgetypes ! edge_type d }

wrapDepots :: EdgeTypes p -> [DepotIO] -> Depots p
wrapDepots et = V.fromList . map (wrapDepot et)

readDepot et = wrapDepot et . read 
readDepots et = wrapDepots et . read 

deriving instance Read t => Read (DepotE t)


{- Show Partial Coset Tables -}

unwrapDepot :: Depot p -> DepotIO
unwrapDepot d = d { edge_type = edgetype_id $ edge_type d }

unwrapDepots = map unwrapDepot . V.toList

showDepot = show . unwrapDepot
showDepots = show . unwrapDepots

instance Show (DepotE (EdgeType p)) where
  show = show . unwrapDepot

deriving instance Show (DepotIO)


{- Initialize Depots -}

{- We note that pub crawls always starts at zero. -}

init_depot e i j = Depot { edge_type = e, idxI = i, idxE = j, idxF = -1, idxL = -1 } 

init_depots e = V.fromList [init_depot e 0 1, init_depot f 1 0]
  where f = complement e 

initialize_depots :: EdgeTypes p -> [Depots p]
initialize_depots edgetypes = map f [0..len-1]
  where len = V.length edgetypes
        f = init_depots . (edgetypes !) 


{- Partial Permutation Building -}

type Permutation t = t -> Maybe t
type LookUp t = Int -> Maybe t
type Indexer t = t -> Int

mkPerm :: LookUp t -> Indexer t -> Permutation t
mkPerm pct p = pct . p

mkPermsR :: LookUp t -> [Indexer t] -> Permutation t
mkPermsR pct ps = foldr (>=>) Just $ map (mkPerm pct) ps

mkPermsL :: LookUp t -> [Indexer t] -> Permutation t
mkPermsL pct ps = foldr (<=<) Just $ map (mkPerm pct) ps 

{- Right action yields EFV = 1 but this executes the left side first  -} 
{- so V . F . E = 1 with usual function composition, i.e. left action -}

mkE = flip mkPerm idxE
mkF = flip mkPerm idxF
mkL = flip mkPerm idxL			{- Finv -}
mkV = flip mkPermsL [idxE, idxL]
mkU = flip mkPermsL [idxF, idxE]	{- Vinv -}


{- Partial Permutation Iteration -}

perm_forbid :: Eq t => t -> (t -> Maybe t) -> (t -> Maybe t)
perm_forbid x p = q
  where q i = if i == x then Nothing else p i

scan_partial_perms :: (Eq t,Show t) => [t -> Maybe t] -> t -> [t]
scan_partial_perms ps d0 = map fromJust . takeWhile (/= Nothing) $
        scanl (>>=) (Just d0) ps
-- ass = and $ map (<3) $ scanl (+) 0 $ map fromNegated $ zipWith notElem l (inits l)
-- Implement frequency counter : http://snippets.dzone.com/posts/show/4263

{- We use right action here because lists are presented left to right.   -}
{- scanl (>>=) z0 l == [ z0, z1@ z0 >>= (l!!0), z2@ z1 >>= (l!!1), ... ] -}
{- scanr (=<<) z0 l == [ z0, z1@ (l!!0) =<< z0, z2@ (l!!1) =<< z1, ... ] -}
{- Both describe the same sequential composition of right actions, but   -}
{- scanl (>>=) resembles a right action while scanr (=<<) more resembles -}
{- a left action.  I believe both exhibit the same strictness properties -}
{- because they're both scans, but conceivably requesting only one term  -}
{- causes a thunk explosion.  If so, use foldl' (>>=) ... instead but    -}
{- remember that foldr works on infinite lists while foldl does not.     -}
-- http://www.haskell.org/haskellwiki/Stack_overflow 
-- http://www.haskell.org/haskellwiki/Foldl_as_foldr 
-- http://hackage.haskell.org/packages/archive/base/latest/doc/html/Prelude.html#v:scanl

modListInt l k = l !! (k `rem` length l)

modListList a b = modListInt a (length b - 1)

cycle_partial_perms :: (Eq t, Show t) => [t -> Maybe t] -> t -> [t]
cycle_partial_perms (p:ps) x = ass res
  where res = scan_partial_perms (p : cycle l) x
        pt = perm_forbid x p
        l = ps ++ [pt]
        pf = modListList (p:ps) res
        ass ll = assert ((last ll) == x || pf (last ll) == Nothing) ll

iterate_partial_perms :: (Eq t, Show t) => (t -> Maybe t) -> t -> [t]
iterate_partial_perms p x = ass $ scan_partial_perms (p : repeat q) x
  where q = perm_forbid x p
        ass l = assert (last l == x || p (last l) == Nothing) l

exhaust_perm_pair :: (Eq t, Show t) => (t -> Maybe t,t -> Maybe t) -> t -> (Bool,[t])
exhaust_perm_pair (p1,p2) d0 = let {
        fun p = tail $ iterate_partial_perms p d0 ;
        test p l = not (null l) && last l == d0 ;
        ls@[l1,l2] = map fun [p1,p2] ;
        ts = zipWith test [p1,p2] ls
   } in if (and ts) then (True,l2) 
        else assert ( not (or ts) || error ("exhaust_perm_pair: " ++ show (zip ts ls)) ) 
          (False, reverse l1 ++ (d0:l2) ) 


duplicate_counts = filter (\(n,v) -> n>1) . map (\x -> (length x,head x)) .
                   group . sort . map idxI
duplicate_warnings l = if null cs then True else (error $ show cs ++ show l)
  where cs = duplicate_counts l


{- Face & Vertex Grouping -}

grouper_vector :: Int -> (Int -> t) -> (t -> [Int]) -> t -> V.Vector t
grouper_vector n find indexes def = V.map (fromMaybe def) $
        foldl' update_null (V.replicate n Nothing) [0..n]
  where update_null vec i = vec // if isNothing (vec ! i) then ups else []
          where l = find i
                ups = zip (filter (<n) $ indexes l) (repeat $ Just l)

group_depots :: (Depot p -> (Bool,[Depot p])) -> Depots p -> V.Vector (Bool,[Depot p])
group_depots depots pct = grouper_vector (V.length pct) find indexes err
  where find = depots . (pct !)
        indexes (b,v) = map idxI v
        err = error "group_depots could not account for all indices"


{- Vertex Verification -}

vertex_depots pct = exhaust_perm_pair (mkU pct, mkV pct)

vertices pct = group_depots (vertex_depots (pct !?)) pct

vertex_depots_cached pct = \d -> tbl ! idxI d 
  where tbl = vertices pct

valency_by_depots (b,l) = length l + fromNegated b

consider_vertex :: (Pongo p) => DepotsF p -> Depot p -> (Bool,Maybe p,Int,[Depot p])
consider_vertex pct d0 = let {
        (b,ds) = vertex_depots pct d0 ;
        valency = valency_by_depots (b,ds) ;
        ps = map (pongo_element . edge_type) ds ;
        p = multiply ps ;
        donetest = accepting (fromJust p) && valency > 2 ;
        dups = duplicate_warnings $ tail ds
   } in assert dups
        (isJust p && (not b || donetest),
         p, valency, ds)

verify_vertex pct = fr . consider_vertex pct
  where fr (b,_,_,_) = b


detect_loop pct x = let {
        y = fromJust $ (mkE pct) x ;
        vd = map idxI . snd . vertex_depots pct ;
        l = intersect (vd x) (vd y)
   } in null l 
--        || trace ("Warning : Loop " ++ show (idxI x) ++ "-" ++ show (idxI y) 
--             ++ " on " ++ show l ++ " found. ") False

detect_loops pct = and (V.toList $ V.map (detect_loop (pct !?)) pct)
                   || trace (showDepots pct) False


{- Face Verification -}

face_depots t = exhaust_perm_pair (mkL t, mkF t)

faces pct = group_depots (face_depots (pct !?)) pct

face_depots_cached pct = \d -> tbl ! idxI d 
  where tbl = faces pct

verify_necklace e es = and $
   map (== (necklace_id $ necklace e)) $
   map (necklace_id . necklace) es
verify_necklace_list (e:es) = verify_necklace e es

consider_face :: DepotsF p -> Depot p -> (Bool,Int,[Depot p])
consider_face pct d0 = let {
        e = edge_type d0 ;
        (b,l) = face_depots pct d0 ;
        ets = map edge_type l ;
        r = (totallength $ necklace e) - sum (map length_beads ets) ;
        rok = if b then r == 0 else r > 0 ;
        beads = and $ zipWith (==) (map end_bead ets) $
            map start_bead $ tail ets ++ (if b then [head ets] else []) ;
        dups = duplicate_warnings $ tail l
   } in assert (dups && verify_necklace e ets)
        (rok && beads, r, l)

available_length pct = fr . consider_face pct
  where fr (_,r,_) = r    {- observe that if b then r == 0 -}

verify_face pct = fr . consider_face pct
  where fr (b,_,_) = b


verify_depot pctf d = verify_vertex pctf d && verify_face pctf d

verify_pct pct = and $ map f $ V.toList pct
  where f = verify_depot (pct !?)

verify_pcts :: (Pongo p) => [Depots p] -> [Depots p]
verify_pcts = filter verify_pct


{- Detect Internal Errors -}

detect_convergence pct = sum res == 0 ||
        error ("Found #(E,F,L)=" ++ show res ++ " convergence errors in " ++ show pct)
  where res = map (length . ddd) [idxE, idxF, idxL]
        ddd p = snd $ V.foldl' f (0::Int, []) $ V.map p pct
        f (!b,!l) !i = if (Bits.testBit b i) then (b, i:l) 
                         else (Bits.setBit b i, l)


        
