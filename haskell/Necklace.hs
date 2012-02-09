
module Necklace where 

import Data.List
import Data.Maybe

import qualified Data.Vector as Vec
import Data.Vector ((!), (!?), (//))

import qualified Data.ByteString.Char8 as BS

import Control.Exception

import Toolbox
import Pongo

{- Necklaces and Edges -}

data Necklace = 
    Necklace {
       necklace_id :: !Int,
       primlen, power :: !Int,
       necklace_name :: !BS.ByteString
    } deriving (Show, Read)

instance Eq Necklace where
  (==) a b = necklace_id a == necklace_id b

totallength n = primlen n * power n

type Necklaces = Vec.Vector Necklace


data EdgeType pongo_t = 
    EdgeType {
       edgetype_id :: !Int,
       start_bead :: !Int, 
       length_beads :: !Int,
       curvature :: !Int,
       pongo_element :: pongo_t,
       complement :: EdgeType pongo_t,
       necklace :: Necklace
    } deriving (Show, Read)
end_bead e = (start_bead e + length_beads e) `rem` (primlen $ necklace e)

{- We record start_bead and end_bead modulo primlen, but length_beads may -}
{- exceed primlen, although length_beads < primlen * power -1             -}

instance Eq (EdgeType pongo_t) where
  (==) a b = edgetype_id a == edgetype_id b && necklace a == necklace b

type EdgeTypes pongo_t = Vec.Vector (EdgeType pongo_t)


{- Convert Necklaces -}

convNecklace eid (prim,pow,nam) = Necklace { 
  necklace_id = eid, primlen = prim, power = pow, necklace_name = nam } 

convNecklaces :: [(Int,Int,BS.ByteString)] -> Necklaces
convNecklaces = Vec.fromList . zipWith convNecklace [0..]

readNecklace [a,b,c] = (fromBS a, fromBS b, c)

readNecklaces :: [[BS.ByteString]] -> Necklaces
readNecklaces = convNecklaces . map readNecklace


{- Convert EdgeTypes -}

type PongoIO = Int

type ParsePongo p = PongoIO -> p

verify_edgetype_pair (a,b) = and $ map f [(a,b), (b,a)]
   where f (x,y) = (complement y) == x

type EdgeTypeIO = (Int,Int,Int,Int,Int,PongoIO)

order_pair (a,b) = swap_by_sign (b-a) (a,b)

convEdgeType :: ParsePongo p -> Necklaces -> Int -> EdgeTypeIO -> ((Int,Int),EdgeType p)
convEdgeType pp necklaces eid (n,sb,lb,cid,curv,pongo) = (
   order_pair (eid,cid-1),
   EdgeType {
        edgetype_id = eid,
        start_bead = sb,
        length_beads = lb,
        curvature = curv,
        pongo_element = pp pongo,
        necklace = necklaces ! (n-1),
        complement = error "Uninitialized complement in EdgeType"
    } )

pairupEdgeTypes :: [((Int,Int),EdgeType p)] -> [EdgeType p]
pairupEdgeTypes ((a2,a):(b2,b):[]) = let {
        x = a { complement = y } ;
        y = b { complement = x }
   } in assert (a2 == b2) $
        x : y : []
pairupEdgeTypes ((a2,a):[]) = let {
        x = a { complement = x } 
   } in x : []
pairupEdgeTypes _ = error "You cannot pair three edges silly!"

convEdgeTypes :: ParsePongo p -> Necklaces -> [EdgeTypeIO] -> EdgeTypes p
convEdgeTypes pp necklaces = Vec.fromList .
        concat . map pairupEdgeTypes . groupUsing (fst . fst) .
        zipWith (convEdgeType pp necklaces) [0..]

readEdgeType [a,b,c,d,e,f] = (fromBS a,fromBS b,fromBS c, fromBS d, fromBS e, fromBS f)

readEdgeTypes :: ParsePongo p -> Necklaces -> [[BS.ByteString]] -> EdgeTypes p
readEdgeTypes pp necklaces = convEdgeTypes pp necklaces . map readEdgeType

readEdgeTypesZ3 = readEdgeTypes parseMultZ3Pongo

showEdgeType e = (edgetype_id e, edgetype_id $ complement e,
        necklace_id $ necklace e,
        start_bead e, length_beads e,
        curvature e, pongo_element e )


{- Read Necklace File -}

fromBS :: BS.ByteString -> Int
fromBS = read . BS.unpack

splitParker :: BS.ByteString -> [[BS.ByteString]]
splitParker = map (filter (not . BS.null) . BS.words) . BS.lines

takeParker :: [[BS.ByteString]] -> ([[BS.ByteString]],[[BS.ByteString]])
takeParker ll = splitAt (fromBS len) (tail ll)
  where (len:info) = head ll ;

takeParkers ll = (a : takeParkers b)
  where (a,b) = takeParker ll

readNecklaceFile :: ParsePongo p -> FilePath -> IO (Int,Necklaces,EdgeTypes p)
readNecklaceFile pp fn = do
        bs <- BS.readFile fn
        let (c:ll) = splitParker bs
        let !circle = fromBS $ head c
	let ps:ns:es:_ = takeParkers ll
	let !necklaces = readNecklaces ns
	let !edgetypes = readEdgeTypes pp necklaces es
        return (circle, necklaces, edgetypes)

readNecklaceFileZ3 = readNecklaceFile parseMultZ3Pongo


