
module ADP.Fusion.Term.Deletion.ForestEdit.LeftLinear where

import Data.Strict.Tuple hiding (fst, snd)
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Prelude hiding (map)

import ADP.Fusion.Core
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.ForestEdit.LeftLinear



instance
  ( TmkCtx1 m ls Deletion (TreeIxL p v a t)
  ) => MkStream m (ls :!: Deletion) (TreeIxL p v a t) where
  mkStream (ls :!: Deletion) sv us is
    = map (\(ss,ee,ii) -> ElmDeletion ii ss)
    . addTermStream1 Deletion sv us is
    $ mkStream ls (termStaticVar Deletion sv is) us (termStreamIndex Deletion sv is)
  {-# Inline mkStream #-}


instance
  ( TstCtx m ts s x0 i0 is (TreeIxL p v a I)
  ) => TermStream m (TermSymbol ts Deletion) s (is:.TreeIxL p v a I) where
  termStream (ts:|Deletion) (cs:.IStatic ()) (us:.u) (is:.TreeIxL frst _ i j)
    = map (\(TState s ii ee) ->
              let RiTilI k l = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL p v a I))
              in  {- traceShow ("-"::String,l,tf) $ -} TState s (ii:.:RiTilI k l) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}


instance TermStaticVar Deletion (TreeIxL p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ i = i
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



