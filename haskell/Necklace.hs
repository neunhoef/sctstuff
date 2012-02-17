{-# OPTIONS_GHC -XStandaloneDeriving -XTypeSynonymInstances -XFlexibleInstances #-}

module Necklace where 

import Data.List
import Data.Maybe
import qualified Data.Vector as V
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

type Necklaces = V.Vector Necklace


data EdgeType pongo_t = 
    EdgeType {
       edgetype_id :: !Int,
       start_bead :: !Int, 
       length_beads :: !Int,
       curvature :: !Int,
       pongo_element :: pongo_t,
       complement :: EdgeType pongo_t,
       necklace :: Necklace
    }
end_bead e = (start_bead e + length_beads e) `rem` (primlen $ necklace e)

{- We record start_bead and end_bead modulo primlen, but length_beads may -}
{- exceed primlen, although length_beads < primlen * power -1             -}

instance Eq (EdgeType pongo_t) where
  (==) a b = edgetype_id a == edgetype_id b && necklace a == necklace b

showableEdgeType e = (edgetype_id e, 
        necklace_id $ necklace e,
        start_bead e, length_beads e,
        edgetype_id $ complement e,
        curvature e, pongo_element e )

instance Show p => Show (EdgeType p) where
  show = show . showableEdgeType

type EdgeTypes pongo_t = V.Vector (EdgeType pongo_t)


{- Convert Necklaces -}

convNecklace eid (prim,pow,nam) = Necklace { 
  necklace_id = eid, primlen = prim, power = pow, necklace_name = nam } 

convNecklaces :: [(Int,Int,BS.ByteString)] -> Necklaces
convNecklaces = V.fromList . zipWith convNecklace [0..]

readNecklace [a,b,c] = (fromBS a, fromBS b, c)

readNecklaces :: [[BS.ByteString]] -> Necklaces
readNecklaces = convNecklaces . map readNecklace


{- Convert Pongo -}

readPongoCayleyTable :: BS.ByteString -> [[BS.ByteString]] -> PongoCayleyTable
readPongoCayleyTable n (bs0:bss) = assert ass pct
  where l = length bss + 1
        rows = V.replicate l 0 : map (V.fromList . (0:) . map fromBS) bss
        pct = PongoCayleyTable {
	    ct_name = n,
	    ct_accepting = V.replicate l False // map (\i -> (fromBS i,True)) bs0,
	    ct_products = V.fromList rows }
	ass = and $ map (== l) $ length rows : map V.length rows

type PongoIO = Int

type ParsePongo p = PongoIO -> p

verifyPongoCayleyTable :: (Pongo p,Show p) => ParsePongo p -> PongoCayleyTable -> Bool
verifyPongoCayleyTable pp ct = (acc && row) || err 
  where l = V.length $ ct_products ct 
        andz = V.and . V.tail
        acc = andz $ V.imap (\i b -> accepting (pp i) == b) $ ct_accepting ct 
        row = andz $ V.imap (\r v -> col (pp r) v) $ ct_products ct 
        col r = andz . V.imap (\c u -> r **** pp c == pp u)
        err = error "Pongo Cayley table failure"


{- Convert EdgeTypes -}

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
convEdgeTypes pp necklaces = V.fromList .
        concat . map pairupEdgeTypes . groupUsing (fst . fst) .
        zipWith (convEdgeType pp necklaces) [0..]

readEdgeType [a,b,c,d,e,f] = (fromBS a,fromBS b,fromBS c, fromBS d, fromBS e, fromBS f)

readEdgeTypes :: ParsePongo p -> Necklaces -> [[BS.ByteString]] -> EdgeTypes p
readEdgeTypes pp necklaces = convEdgeTypes pp necklaces . map readEdgeType

readEdgeTypesZ3 = readEdgeTypes parseMultZ3Pongo


{- Read Necklace File -}

fromBS :: BS.ByteString -> Int
fromBS = read . BS.unpack

splitParker :: BS.ByteString -> [[BS.ByteString]]
splitParker = map (filter (not . BS.null) . BS.words) . BS.lines

takeParker :: [[BS.ByteString]] -> ([[BS.ByteString]],[[BS.ByteString]])
takeParker ll = (info:a,b)
  where (a,b) = splitAt (fromBS len) (tail ll)
        (len:info) = head ll

takeParkers ll = (a : takeParkers b)
  where (a,b) = takeParker ll

data NeckFile pongo_t = NeckFile {
        nf_circle :: !Int,
        nf_caleytable :: !PongoCayleyTable,
        nf_necklaces :: !Necklaces,
        nf_edgetypes :: EdgeTypes pongo_t
    } deriving (Show)

readNecklaceFile :: (Pongo p,Show p) => ParsePongo p -> FilePath -> IO (NeckFile p)
readNecklaceFile pp fn = do
        bs <- BS.readFile fn
        let (cnt:ll) = splitParker bs
        let circle = fromBS $ head cnt
	let cs:ns:es:_ = takeParkers ll
	let caleytable = readPongoCayleyTable (BS.pack "") cs
	let ass = verifyPongoCayleyTable pp caleytable 
	      || error "Pongo doesn't match Cayley table"
	let necklaces = readNecklaces (tail ns)
	let edgetypes = readEdgeTypes pp necklaces (tail es)
        return $ assert ass $ NeckFile {
	    nf_circle = circle,
	    nf_caleytable = caleytable, 
	    nf_necklaces = necklaces,
	    nf_edgetypes = edgetypes }


readNecklaceFileTrivial = readNecklaceFile
        parseTrivialPongo
readNecklaceFileZ3 = readNecklaceFile 
        parseMultZ3Pongo
-- readNecklaceFileCayleyTable = readNecklaceFile 
--        parseCayleyTablePongo

