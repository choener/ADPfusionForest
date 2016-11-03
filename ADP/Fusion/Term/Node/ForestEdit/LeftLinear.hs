
-- | 'Node' handling for tree-editing.
--
-- TODO outside

module ADP.Fusion.Term.Node.ForestEdit.LeftLinear where

import           Data.Strict.Tuple hiding (fst, snd)
import           Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import           Prelude hiding (map)
import qualified Prelude as P

import           ADP.Fusion.Core
import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Core.ForestEdit.LeftLinear
import           ADP.Fusion.Term.Node.Type



instance
  ( TmkCtx1 m ls (Node r x) (TreeIxL p v a t)
  ) => MkStream m (ls :!: Node r x) (TreeIxL p v a t) where
  mkStream (ls :!: Node f xs) sv us is
    = map (\(ss,ee,ii) -> ElmNode ee ii ss)
    . addTermStream1 (Node f xs) sv us is
    $ mkStream ls (termStaticVar (Node f xs) sv is) us (termStreamIndex (Node f xs) sv is)
  {-# Inline mkStream #-}


instance
  ( TstCtx m ts s x0 i0 is (TreeIxL p v a I)
  ) => TermStream m (TermSymbol ts (Node r x)) s (is:.TreeIxL p v a I) where
  termStream (ts:|Node f xs) (cs:.IStatic ()) (us:.TreeIxL _ _ l u) (is:.TreeIxL frst _ i j)
    = map (\(TState s ii ee) -> {-traceShow ('n',i,j) $-} TState s (ii:.:RiTilI (j-1) j) (ee:.f xs (j-1)) )
    . termStream ts cs us is
    . staticCheck (i<j)
  {-# Inline termStream #-}


instance TermStaticVar (Node r x) (TreeIxL p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (TreeIxL frst c i j) = TreeIxL frst c i $ j-1
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}


