module Data.Forest.Static.Left where

import           Data.Either (either)
import           Data.Graph.Inductive.Basic
import           Data.Traversable (mapAccumL)
--import qualified Data.Map.Strict as S
import qualified Data.Tree as T
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import           Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import           Prelude hiding (map)
import           Debug.Trace
import           Data.Strict.Tuple hiding (fst, snd)
import qualified Data.Forest.Static as F
import Biobase.Newick

import           Data.Forest.Static
import           Data.Forest.Static.Node
import           ADP.Fusion
import           Data.PrimitiveArray hiding (map)
import           ADP.Fusion.SynVar.Indices


data TreeIxL p v a t = TreeIxL !(Forest p v a) !(VU.Vector Int) !Int !Int

instance Show (TreeIxL p v a t) where
  show (TreeIxL _ _ i j) = show (i,j)

minIx, maxIx :: Forest p v a -> TreeIxL p v a t
minIx f = TreeIxL f (leftMostChildren f) 0 (VU.length (parent f))

maxIx f = TreeIxL f (leftMostChildren f) 0 (VU.length (parent f))
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



--Node

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
    = map (\(TState s ii ee) -> traceShow ('n',i,j) $ TState s (ii:.:RiTilI (j-1) j) (ee:.f xs (j-1)) )
    . termStream ts cs us is
    . staticCheck (i<j)
--  termStream (ts:|Node f xs) (cs:.IVariable ()) (us:.TreeIxL _ _ l u) (is:.TreeIxL frst _ i j)
--    = map (\(TState s ii ee) -> traceShow ('m',i,j) $ TState s (ii:.:RiTilI i (i+1)) (ee:.f xs i) )
--    . termStream ts cs us is
--    . staticCheck (i<j)
  {-# Inline termStream #-}


instance TermStaticVar (Node r x) (TreeIxL p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (TreeIxL frst c i j) = TreeIxL frst c i $ j-1
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}


--Epsilon

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



--deletion

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
--    . staticCheck (ii == T)
  {-# Inline termStream #-}


instance TermStaticVar Deletion (TreeIxL p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ i = i
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



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



--synVar

instance
  ( IndexHdr s x0 i0 us (TreeIxL p v a I) cs c is (TreeIxL p v a I)
  , MinSize c
  , Show a, VG.Vector v a -- TEMP!
  , a ~ Info
  ) => AddIndexDense s (us:.TreeIxL p v a I) (cs:.c) (is:.TreeIxL p v a I) where
  addIndexDenseGo (cs:._) (vs:.IStatic ()) (us:.TreeIxL frst lc l u) (is:.TreeIxL _ _ i j)  -- static = rechts!
    = map go . addIndexDenseGo cs vs us is
    where
      go (SvS s tt ii) =
        let RiTilI _ k = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL p v a I))
        in SvS s (tt:.TreeIxL frst lc k j) (ii:.:RiTilI k j)
  addIndexDenseGo (cs:._) (vs:.IVariable ()) (us:.TreeIxL frst lc l u) (is:.TreeIxL _ _ i j) --variable = links!
    = map go . addIndexDenseGo cs vs us is . staticCheck (i<j)
    where
      go (SvS s tt ii) =
        let RiTilI _ k = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL p v a I))
            l = lc VG.! (j-1)
        in SvS s (tt:.TreeIxL frst lc k l) (ii:.:RiTilI k l)
{-    = flatten mk step . addIndexDenseGo cs vs us is
      where
        mk s = 
          let ss = if ps == -1 then roots frst else (children frst) VG.! ps
              ps = parent frst VG.! i
              rm = traceShow ('r',i,j) $ if i==j then j else VG.last $ VG.filter (<j) ss
          in return (s,rm)
        step ((SvS s tt ii),k)
          | k==j = return $ Done
          | otherwise = return $ Yield (SvS s (tt:.TreeIxL frst lc i k) (ii:.:RiTilI i k)) ((SvS s tt ii),j)
        {-# Inline [0] mk #-}
        {-# Inline [0] step #-}
-}
  {-# Inline addIndexDenseGo #-}


instance (MinSize c) => TableStaticVar u c (TreeIxL p v a I) where 
  tableStaticVar _ _ _ _ = IVariable ()
  tableStreamIndex _ c _ = id
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}


