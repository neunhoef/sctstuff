
module Graphing where 

import Data.List
import Data.Maybe

import qualified Data.Vector as Vec
import Data.Vector ((!), (!?), (//))

import Control.Monad

import Data.Rotations
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

graph_pct_canvas pct i = runGraphvizCanvas TwoPi g Xlib
  where g = digraph (Int i) $ sequence $ edges pct

graph_pct_command pct i fn = runGraphvizCommand TwoPi g Jpeg fn
  where g = digraph (Int i) $ sequence $ edges pct



