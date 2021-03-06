
-- | 'Node' handling for tree-editing.
--
-- TODO outside

module ADP.Fusion.Term.Node.ForestEdit.LeftLinear where

import           Data.Strict.Tuple hiding (fst, snd)
import           Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import           Prelude hiding (map)
import qualified Prelude as P
import qualified Data.Vector.Generic as VG

import           ADP.Fusion.Core
import           Data.PrimitiveArray hiding (map)
import           Data.Forest.Static

import           ADP.Fusion.Core.ForestEdit.LeftLinear
import           ADP.Fusion.Term.Node.Type



-- * Common

instance
  ( TmkCtx1 m ls (Node r x) (TreeIxL p v a t)
  ) => MkStream m (ls :!: Node r x) (TreeIxL p v a t) where
  mkStream (ls :!: Node f nty xs) sv us is
    = map (\(ss,ee,ii) -> ElmNode ee ii ss)
    . addTermStream1 (Node f nty xs) sv us is
    $ mkStream ls (termStaticVar (Node f nty xs) sv is) us (termStreamIndex (Node f nty xs) sv is)
  {-# Inline mkStream #-}



-- * Inside

instance
  ( TstCtx m ts s x0 i0 is (TreeIxL p v a I)
  ) => TermStream m (TermSymbol ts (Node r x)) s (is:.TreeIxL p v a I) where
  termStream (ts:|Node f nty xs) (cs:.IStatic ()) (us:.TreeIxL _ _ l u) (is:.TreeIxL frst lc i j)
    = map (\(TState s ii ee) -> {-traceShow ('n',i,j) $-} TState s (ii:.:RiTilI (j-1) j) (ee:.f xs (j-1)) )
    . termStream ts cs us is
    . staticCheck (i < j && (nty == NTany || i == lc VG.! (j-1)) )
    -- TODO this check should only be @i<j@, but we want to test more with
    -- SingleEdit where only have this for actual trees
  {-# Inline termStream #-}


instance TermStaticVar (Node r x) (TreeIxL p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (TreeIxL frst c i j) = TreeIxL frst c i $ j-1
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



-- * Outside
--
-- basically, we have a missing forest (@-0@ and @-1@) and if we have this
-- and an existing (@2@) node, then before we had a missing tree. So
-- @\hat{F} -> \hat{T} x@, for example.
--
-- @
--              2         -2
--   / \    +       =     / \
--  -0 -1                -0 -1
-- @

instance
  ( TstCtx m ts s x0 i0 is (TreeIxL Post v a O)
  ) => TermStream m (TermSymbol ts (Node r x)) s (is:.TreeIxL Post v a O) where
  termStream (ts:|Node f nty xs) (cs:.OStatic ()) (us:.TreeIxL _ _ l u) (is:.TreeIxL frst lc i j)
    = map (\(TState s ii ee) -> let RiTilO _ _ oi oj = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL Post v a O))
            -- given an index @[i,j)@ of "missing" structure, we add a new
            -- node at @[j,j+1)@.
            in TState s (ii:.:RiTilO j (j+1) oi oj) (ee:.f xs j) )
    . termStream ts cs us is
    . staticCheck (i <= j && j < u && (nty == NTany || j < u && i == lc VG.! j) )
    -- TODO same here, check is only for SingleEdit. If this works out,
    -- we'll actually need special tree-root nodes for Tree-Editing.
  {-# Inline termStream #-}



instance TermStaticVar (Node r x) (TreeIxL Post v a O) where
  termStaticVar _ sv _ = sv -- context doesn't change
  termStreamIndex _ _ (TreeIxL frst c i j) = TreeIxL frst c i $ j+1
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



