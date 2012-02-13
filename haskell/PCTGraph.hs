
module PCTGraph where 

import Data.List
import Data.Maybe

import qualified Data.Vector as Vec
import Data.Vector ((!), (!?), (//))

import Control.Monad

import Toolbox
import Pongo
import Necklace
import ParCosetTabel
import PubCrawl

import Data.GraphViz.Attributes
import Data.GraphViz.Commands
import Data.GraphViz.Types.Monadic


{- Depots -}

vertex_colors = map fst . Vec.toList . vertices

{- We should theoretically get canonical vertex names from all forms below -}

vertex_name_fast pct = idxI . head . snd . vdc 
  where vdc = vertex_depots_cached pct

vertex_name_min pct = minimum . map idxI . snd . vertex_depots (pct !?)

vertex_name_list pct = show . minimumRotation . map idxI . snd . vertex_depots (pct !?)


edges pct = map (\d -> edge (vn d) (vn $ imgE d) [ve d]) $ Vec.toList pct
  where vn = vertex_name_list pct 
        ve = toLabel . idxI
        imgE d = pct ! idxE d

graph_pct pct i = runGraphvizCanvas TwoPi g Xlib
  where g = digraph (Int i) $ sequence $ edges pct


{- CrawlExtend Tree -}

crawl_extend_tree circle edgetypes n t = runGraphvizCanvas TwoPi g Xlib
  where g = digraph (Int 0) $ do 
            node (fst t) [shape MDiamond] 
            cetree n t
        do_ce crpct = do_crawl_extend circle edgetypes [crpct]
        cetree 0 _ = return ()
        cetree k (s,ce) = do
            let (_,_,m) = ce
            node s [toLabel ""]
            let l = zip (map (\i -> s ++ "." ++ show i) [0..]) $ map do_ce m
            mapM_ (cetree (k-1)) l
            sequence_ $ zipWith (edge s) (map fst l) $
                  map (\i -> [toLabel (i::Int)]) [0..]


