
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

import Data.GraphViz.Commands
import Data.GraphViz.Types.Monadic


{- Depots -}

vertex_colors = map fst . Vec.toList . vertices

{- We should theoretically get canonical vertex names from all forms below -}

vertex_name_fast pct = idxI . head . snd . vdc 
  where vdc = vertex_depots_cached pct

vertex_name_min pct = minimum . map idxI . snd . vertex_depots (pct !?)

vertex_name_list pct = show . map idxI . snd . vertex_depots (pct !?)


edges pct = map (\d -> (vn d) --> (vn $ imgE d)) $ Vec.toList pct
  where vn = vertex_name_list pct 
        imgE d = pct ! idxE d

graph_pct pct i = runGraphvizCanvas TwoPi g Xlib
  where g = digraph (Int i) $ sequence $ edges pct


{- CrawlExtend Tree -}

crawl_extend_tree circle edgetypes n t = runGraphvizCanvas TwoPi g Xlib
  where g = digraph (Int n) $ cetree t
        cetree (s,ce) = do
            let (_,_,m) = ce 
            let l = zip (map (\i -> s ++ "." ++ show i) [0..]) $
                    map (\crpct -> do_crawl_extend circle edgetypes [crpct]) m
            mapM_ cetree l
            sequence_ $ map (\i -> s --> fst i) l


