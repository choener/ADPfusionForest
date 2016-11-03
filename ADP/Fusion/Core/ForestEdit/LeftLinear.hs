
module ADP.Fusion.Core.ForestEdit.LeftLinear where

import           Data.Either (either)
import           Data.Graph.Inductive.Basic
import           Data.Strict.Tuple hiding (fst, snd)
import           Data.Traversable (mapAccumL)
import           Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import           Debug.Trace
import           Prelude hiding (map)
import qualified Data.Forest.Static as F
import qualified Data.Tree as T
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU

import           ADP.Fusion.Core
import           Data.Forest.Static
import           Data.PrimitiveArray hiding (map)
import           Math.TriangularNumbers

import           ADP.Fusion.Term.Node.Type



data TreeIxL p v a t = TreeIxL !(Forest p v a) !(VU.Vector Int) !Int !Int

instance Show (TreeIxL p v a t) where
  show (TreeIxL _ _ i j) = show (i,j)

minIx, maxIx :: Forest p v a -> TreeIxL p v a t
minIx f = TreeIxL f (leftMostLeaves f) 0 (VU.length (parent f))

maxIx f = TreeIxL f (leftMostLeaves f) 0 (VU.length (parent f))
{-# Inline minIx #-}
{-# Inline maxIx #-}


data instance RunningIndex (TreeIxL p v a I) = RiTilI !Int !Int

instance Index (TreeIxL p v a t) where
  -- | trees @T@ are stored in the first line, i.e. @+0@, forests @F@ (with
  -- @j==u@ are stored in the second line, i.e. @+u+1@ to each index.
  linearIndex _ (TreeIxL _ _ l u) (TreeIxL _ _ i j)
    = linearIndex (subword 0 0) (subword l u) (subword i j)
  {-# Inline linearIndex #-}
  smallestLinearIndex _ = error "still needed?"
  {-# Inline smallestLinearIndex #-}
  largestLinearIndex (TreeIxL _ _ _ u) = (triangularNumber $ u-0+1) - 1
  {-# Inline largestLinearIndex #-}
  size _ (TreeIxL _ _ _ u) = triangularNumber $ u-0+1
  {-# Inline size #-}
  inBounds _ (TreeIxL _ _ _ u) (TreeIxL _ _ i j) = 0 <= i && i <= j && j <= u
  {-# Inline inBounds #-}


instance IndexStream z => IndexStream (z:.TreeIxL p v a I) where
  streamUp   (ls:.TreeIxL p c lf _) (hs:.TreeIxL _ _ _ ht) = flatten (streamUpMk lf  ht) (streamUpStep  p c lf ht) $ streamUp ls hs
  streamDown (ls:.TreeIxL p c lf _) (hs:.TreeIxL _ _ _ ht) = flatten (streamDownMk lf ht) (streamDownStep p c lf ht) $ streamDown ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}

streamUpMk l h z = return (z,0,0)  -- start with size 0 and smallest element 0
{-# Inline [0] streamUpMk #-}

streamUpStep p c lf ht (z,s,i)  -- s=size, i=left border
  | s > VG.length c     = return $ SM.Done
  | i + s > VG.length c = return $ SM.Skip (z,s+1,0)
  | otherwise = return $ SM.Yield (z:.TreeIxL p c i (i+s)) (z,s,i+1)
{-# Inline [0] streamUpStep #-}

streamDownMk lf ht z = return (z,ht,0)
{-# Inline [0] streamDownMk #-}

streamDownStep p c lf ht (z,s,i)
  | s < 0     = return $ SM.Done
  | i < 0     = return $ SM.Skip (z,s-1,ht-(s-1))
  | otherwise = return $ SM.Yield (z:.TreeIxL p c i (i+s)) (z,s,i-1)
{-# Inline [0] streamDownStep #-}


instance IndexStream (Z:.TreeIxL p v a t) => IndexStream (TreeIxL p v a t)

instance RuleContext (TreeIxL p v a I) where
  type Context (TreeIxL p v a I) = InsideContext ()
  initialContext _ = IStatic ()
  {-# Inline initialContext #-}



-- Invisible starting symbol

instance (Monad m) => MkStream m S (TreeIxL p v a I) where
  mkStream S (IStatic ()) (TreeIxL frst _ l u) (TreeIxL _ _ i j)
    = staticCheck (i>=0 && i==j && j<=u) . singleton . ElmS $ RiTilI i i
  mkStream S (IVariable ()) (TreeIxL frst _ l u) (TreeIxL _ _ i j)
    = staticCheck (i>=0 && i<=j && j<=u) . singleton . ElmS $ RiTilI i i
  {-# Inline mkStream #-}


instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.TreeIxL p v a I) where
  mkStream S (vs:.IStatic()) (lus:.TreeIxL frst _ l u) (is:.TreeIxL _ _ i j)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiTilI i i)
    . staticCheck (i>=0 && i==j && j<=u)
    $ mkStream S vs lus is
  mkStream S (vs:.IVariable()) (lus:.TreeIxL frst _ l u) (is:.TreeIxL _ _ i j)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiTilI i i)
    . staticCheck (i>=0 && i<=j && j<=u)
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}

