
-- | Data structures and instances to combine efficient 'Forest' structures
-- with @ADPfusion@.

module Data.Forest.Static.ADP where

import           Data.Either (either)
import           Data.Graph.Inductive.Basic
import           Data.Traversable (mapAccumL)
import qualified Data.Map.Strict as S
import qualified Data.Tree as T
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Fusion.Stream.Monadic as SM

import           Data.Forest.Static
import           ADP.Fusion
import           Data.PrimitiveArray



data TreeIxR p v a t = TreeIxR !(Forest p v a) !Int !Int

data instance RunningIndex (TreeIxR p v a I) = RiTirI !Int

instance Index (TreeIxR p v a t) where
  linearIndex _ _ (TreeIxR _ l _) = l
  {-# Inline linearIndex #-}
  smallestLinearIndex _ = error "still needed?"
  {-# Inline smallestLinearIndex #-}
  largestLinearIndex (TreeIxR p _ _) = VU.length (parent p)
  {-# Inline largestLinearIndex #-}
  size _ (TreeIxR p _ _) = VU.length (parent p) + 1
  {-# Inline size #-}
  inBounds _ (TreeIxR p _ _) (TreeIxR _ l r) = 0 <= l && r <= VU.length (parent p)
  {-# Inline inBounds #-}


instance IndexStream z => IndexStream (z:.TreeIxR p v a I) where
  streamUp   (ls:.TreeIxR p lf _) (hs:.TreeIxR _ _ ht) = flatten (streamUpMk   ht) (streamUpStep   p lf ht) $ streamUp ls hs
  streamDown (ls:.TreeIxR p lf _) (hs:.TreeIxR _ _ ht) = flatten (streamDownMk lf) (streamDownStep p lf ht) $ streamDown ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}

streamUpMk ht z = return (z,ht)
{-# Inline [0] streamUpMk #-}

streamUpStep p lf ht (z,k)
  | k < lf    = return $ SM.Done
  | otherwise = return $ SM.Yield (z:.TreeIxR p k ht) (z,k-1)
{-# Inline [0] streamUpStep #-}

streamDownMk lf z = return (z,lf)
{-# Inline [0] streamDownMk #-}

streamDownStep p lf ht (z,k)
  | k > ht    = return $ SM.Done
  | otherwise = return $ SM.Yield (z:.TreeIxR p k ht) (z,k+1)
{-# Inline [0] streamDownStep #-}


instance IndexStream (Z:.TreeIxR p v a t) => IndexStream (TreeIxR p v a t)

