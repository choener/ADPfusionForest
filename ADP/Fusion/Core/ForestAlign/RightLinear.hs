
-- | Data structures and instances to combine efficient 'Forest' structures
-- with @ADPfusion@.

module ADP.Fusion.Core.ForestAlign.RightLinear where

import           Control.Exception (assert)
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

import           ADP.Fusion.Term.Node.Type



data TreeIxR p v a t = TreeIxR !(Forest p v a) !Int !TF

instance Show (TreeIxR p v a t) where
  show (TreeIxR _ i j) = show (i,j)

minIx, maxIx :: Forest p v a -> TreeIxR p v a t
minIx f = TreeIxR f 0 minBound

maxIx f = TreeIxR f (VU.length (parent f)) maxBound
{-# Inline minIx #-}
{-# Inline maxIx #-}

data TF = F | T | E
  deriving (Show,Eq,Ord,Enum,Bounded)

instance Index TF where
  linearIndex _ _ tf = fromEnum tf
  {-# Inline linearIndex #-}
  smallestLinearIndex _ = fromEnum (minBound :: TF)
  {-# Inline smallestLinearIndex #-}
  largestLinearIndex _ = fromEnum (maxBound :: TF)
  {-# Inline largestLinearIndex #-}
  size _ _ = fromEnum (maxBound :: TF) + 1
  {-# Inline size #-}
  inBounds _ u k = k <= u
  {-# Inline inBounds #-}


data instance RunningIndex (TreeIxR p v a I) = RiTirI !Int !TF

instance Index (TreeIxR p v a t) where
  -- | trees @T@ are stored in the first line, i.e. @+0@, forests @F@ (with
  -- @j==u@ are stored in the second line, i.e. @+u+1@ to each index.
  linearIndex (TreeIxR _ l ll) (TreeIxR _ u uu) (TreeIxR _ k tf)
    = (fromEnum (maxBound :: TF) + 1) * k + fromEnum tf
  {-# Inline linearIndex #-}
  smallestLinearIndex _ = error "still needed?"
  {-# Inline smallestLinearIndex #-}
  largestLinearIndex (TreeIxR p u ut) = (fromEnum (maxBound :: TF) + 1) * u + fromEnum (maxBound :: TF)
  {-# Inline largestLinearIndex #-}
  size (TreeIxR _ l ll) (TreeIxR _ u uu) = (fromEnum (maxBound :: TF) + 1) * (u+1)
  {-# Inline size #-}
  inBounds (TreeIxR _ l _) (TreeIxR _ u _) (TreeIxR _ k _) = l <= k && k <= u
  {-# Inline inBounds #-}


instance IndexStream z => IndexStream (z:.TreeIxR p v a I) where
  streamUp   (ls:.TreeIxR p lf _) (hs:.TreeIxR _ ht _) = flatten (streamUpMk   lf ht) (streamUpStep   p lf ht) $ streamUp ls hs
  streamDown (ls:.TreeIxR p lf _) (hs:.TreeIxR _ ht _) = flatten (streamDownMk lf ht) (streamDownStep p lf ht) $ streamDown ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}

streamUpMk lf ht z = return (z,ht,maxBound :: TF)
{-# Inline [0] streamUpMk #-}

streamUpStep p lf ht (z,k,tf)
  | k < lf         = return $ SM.Done
  | tf == minBound = return $ SM.Yield (z:.TreeIxR p k tf) (z,k-1,maxBound)
  | otherwise      = return $ SM.Yield (z:.TreeIxR p k tf) (z,k,pred tf)
{-# Inline [0] streamUpStep #-}

streamDownMk lf ht z = return (z,lf,minBound :: TF)
{-# Inline [0] streamDownMk #-}

streamDownStep p lf ht (z,k,tf)
  | k > ht         = return $ SM.Done
  | tf == maxBound = return $ SM.Yield (z:.TreeIxR p k tf) (z,k+1,minBound)
  | otherwise      = return $ SM.Yield (z:.TreeIxR p k tf) (z,k,succ tf)
{-# Inline [0] streamDownStep #-}


instance IndexStream (Z:.TreeIxR p v a t) => IndexStream (TreeIxR p v a t)

instance RuleContext (TreeIxR p v a I) where
  type Context (TreeIxR p v a I) = InsideContext ()
  initialContext _ = IStatic ()
  {-# Inline initialContext #-}



-- Invisible starting symbol

instance (Monad m) => MkStream m S (TreeIxR p v a I) where
  mkStream S _ (TreeIxR frst u ut) (TreeIxR _ k kt)
    = staticCheck (k>=0 && k<=u) . singleton . ElmS $ RiTirI k kt
  {-# Inline mkStream #-}


instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.TreeIxR p v a I) where
  mkStream S (vs:._) (lus:.TreeIxR frst u ut) (is:.TreeIxR _ k kt)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiTirI k kt)
    . staticCheck (k>=0 && k<=u)
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}



-- * Outside instances

-- | Outside running index structure requires two local index structures.
-- One is for the inside symbols, one for the outside symbol.

data instance RunningIndex (TreeIxR p v a O) = RiTirO !Int !TF !Int !TF -- I, I, O, O

-- | Outside works in the opposite direction.
--
-- TODO check if the original @Up@ / @Down@ combination is ok.

instance IndexStream z => IndexStream (z:.TreeIxR p v a O) where
  streamUp   (ls:.TreeIxR p lf _) (hs:.TreeIxR _ ht _) = flatten (streamDownMk lf ht) (streamDownStep p lf ht) $ streamUp ls hs
  streamDown (ls:.TreeIxR p lf _) (hs:.TreeIxR _ ht _) = flatten (streamUpMk   lf ht) (streamUpStep   p lf ht) $ streamDown ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}

instance RuleContext (TreeIxR p v a O) where
  type Context (TreeIxR p v a O) = OutsideContext ()
  initialContext _ = OStatic ()
  {-# Inline initialContext #-}







-- Invisible starting symbol

instance (Monad m) => MkStream m S (TreeIxR p v a O) where
  mkStream S _ (TreeIxR frst u ut) (TreeIxR _ k kt)
    = staticCheck (k>=0 && k<=u) . singleton . ElmS $ RiTirO k kt k kt
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.TreeIxR p v a O) where
  mkStream S (vs:._) (lus:.TreeIxR frst u ut) (is:.TreeIxR _ k kt)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiTirO k kt k kt)
    . staticCheck (k>=0 && k<=u)
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}




-- * Complemented instances

-- | Outside running index structure requires two local index structures.
-- One is for the inside symbols, one for the outside symbol.

data instance RunningIndex (TreeIxR p v a C) = RiTirC !Int !TF

-- | Outside works in the opposite direction.
--
-- TODO check if the original @Up@ / @Down@ combination is ok.

instance IndexStream z => IndexStream (z:.TreeIxR p v a C) where
  streamUp   (ls:.TreeIxR p lf _) (hs:.TreeIxR _ ht _) = flatten (streamUpMk   lf ht) (streamUpStep   p lf ht) $ streamUp ls hs
  streamDown (ls:.TreeIxR p lf _) (hs:.TreeIxR _ ht _) = flatten (streamDownMk lf ht) (streamDownStep p lf ht) $ streamDown ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}

instance RuleContext (TreeIxR p v a C) where
  type Context (TreeIxR p v a C) = ComplementContext
  initialContext _ = Complemented
  {-# Inline initialContext #-}



-- Invisible starting symbol

instance (Monad m) => MkStream m S (TreeIxR p v a C) where
  mkStream S _ (TreeIxR frst u ut) (TreeIxR _ k kt)
    = staticCheck (k>=0 && k<=u) . singleton . ElmS $ RiTirC k kt
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.TreeIxR p v a C) where
  mkStream S (vs:._) (lus:.TreeIxR frst u ut) (is:.TreeIxR _ k kt)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiTirC k kt)
    . staticCheck (k>=0 && k<=u)
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}



