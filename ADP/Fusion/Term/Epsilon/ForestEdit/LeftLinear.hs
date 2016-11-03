
module ADP.Fusion.Term.Epsilon.ForestEdit.LeftLinear where

import Data.Strict.Tuple hiding (fst, snd)
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Prelude hiding (map)

import ADP.Fusion.Core
import Data.Forest.Static
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.ForestEdit.LeftLinear



instance
  ( TmkCtx1 m ls Epsilon (TreeIxL p v a t)
  ) => MkStream m (ls :!: Epsilon) (TreeIxL p v a t) where
  mkStream (ls :!: Epsilon) sv us is
    = map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}


instance
  ( TstCtx m ts s x0 i0 is (TreeIxL p v a I)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.TreeIxL p v a I) where
  termStream (ts:|Epsilon) (cs:.IStatic ()) (us:.TreeIxL _ _ l u) (is:.TreeIxL frst _ i j)
    = map (\(TState s ii ee) -> TState s (ii:.:RiTilI i j) (ee:.()) )
    . termStream ts cs us is
    . staticCheck (i==j)
  {-# Inline termStream #-}


instance TermStaticVar Epsilon (TreeIxL p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ i = i
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



