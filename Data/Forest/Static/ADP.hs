
-- | Data structures and instances to combine efficient 'Forest' structures
-- with @ADPfusion@.

module Data.Forest.Static.ADP where

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

import           Data.Forest.Static
import           ADP.Fusion
import           Data.PrimitiveArray hiding (map)
import           ADP.Fusion.SynVar.Indices


data TreeIxR p v a t = TreeIxR !(Forest p v a) !Int !Int
  deriving Show

minIx, maxIx :: Forest p v a -> TreeIxR p v a t
minIx f = TreeIxR f 0 0

maxIx f = TreeIxR f 0 (VU.length (parent f) -1)
{-# Inline minIx #-}
{-# Inline maxIx #-}

data instance RunningIndex (TreeIxR p v a I) = RiTirI !Int

instance Index (TreeIxR p v a t) where
  linearIndex _ _ (TreeIxR _ l _) = l
  {-# Inline linearIndex #-}
  smallestLinearIndex _ = error "still needed?"
  {-# Inline smallestLinearIndex #-}
  largestLinearIndex (TreeIxR p _ _) = VU.length (parent p)
  {-# Inline largestLinearIndex #-}
  size _ (TreeIxR p _ _) = VU.length (parent p) + 2 -- epsilon mapping
  {-# Inline size #-}
  inBounds _ (TreeIxR p _ _) (TreeIxR _ l r) = 0 <= l && r <= VU.length (parent p)
  {-# Inline inBounds #-}


instance IndexStream z => IndexStream (z:.TreeIxR p v a I) where
  streamUp   (ls:.TreeIxR p lf _) (hs:.TreeIxR _ _ ht) = flatten (streamUpMk   ht) (streamUpStep   p lf ht) $ streamUp ls hs
  streamDown (ls:.TreeIxR p lf _) (hs:.TreeIxR _ _ ht) = flatten (streamDownMk lf) (streamDownStep p lf ht) $ streamDown ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}

streamUpMk ht z = return (z,ht+1)
{-# Inline [0] streamUpMk #-}

streamUpStep p lf ht (z,k)
  | k < lf    = return $ SM.Done
  | otherwise = return $ SM.Yield (z:.TreeIxR p k ht) (z,k-1)
{-# Inline [0] streamUpStep #-}

streamDownMk lf z = return (z,lf)
{-# Inline [0] streamDownMk #-}

streamDownStep p lf ht (z,k)
  | k > ht+1    = return $ SM.Done
  | otherwise = return $ SM.Yield (z:.TreeIxR p k ht) (z,k+1)
{-# Inline [0] streamDownStep #-}


instance IndexStream (Z:.TreeIxR p v a t) => IndexStream (TreeIxR p v a t)

instance RuleContext (TreeIxR p v a I) where
  type Context (TreeIxR p v a I) = InsideContext ()
  initialContext _ = IStatic ()
  {-# Inline initialContext #-}


data Node r x where
  Node :: VG.Vector v x
       => (v x -> Int -> r)
       -> !(v x)
       -> Node r x

node :: VG.Vector v x => v x -> Node x x
node = Node VG.unsafeIndex
{-# Inline node #-}

instance Build (Node r x)

instance
  ( Element ls i
  ) => Element (ls :!: Node r x) i where
    data Elm (ls :!: Node r x) i = ElmNode !r !(RunningIndex i) !(Elm ls i)
    type Arg (ls :!: Node r x)   = Arg ls :. r
    getArg (ElmNode x _ ls) = getArg ls :. x
    getIdx (ElmNode _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}


type instance TermArg (Node r x) = r


instance
  ( TmkCtx1 m ls (Node r x) (TreeIxR p v a t)
  ) => MkStream m (ls :!: Node r x) (TreeIxR p v a t) where
  mkStream (ls :!: Node f xs) sv us is
    = map (\(ss,ee,ii) -> ElmNode ee ii ss)
    . addTermStream1 (Node f xs) sv us is
    $ mkStream ls (termStaticVar (Node f xs) sv is) us (termStreamIndex (Node f xs) sv is)
  {-# Inline mkStream #-}


instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a I)
  ) => TermStream m (TermSymbol ts (Node r x)) s (is:.TreeIxR p v a I) where
  termStream (ts:|Node f xs) (cs:.IVariable ()) (us:.u) (is:.TreeIxR frst i j)
    = map (\(TState s ii ee) ->
              let RiTirI l = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
              in  TState s (ii:.:RiTirI (l+1)) (ee:.f xs l) )
    . termStream ts cs us is
    . staticCheck (i<=j)
  {-# Inline termStream #-}


instance TermStaticVar (Node r x) (TreeIxR p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (TreeIxR frst i j) = TreeIxR frst i j
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}


--Epsilon

instance
  ( TmkCtx1 m ls Epsilon (TreeIxR p v a t)
  ) => MkStream m (ls :!: Epsilon) (TreeIxR p v a t) where
  mkStream (ls :!: Epsilon) sv us is
    = map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}


instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a I)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.TreeIxR p v a I) where
  termStream (ts:|Epsilon) (cs:.IStatic ()) (us:.u) (is:.TreeIxR frst i j)
    = map (\(TState s ii ee) ->
              let RiTirI l = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
              in  TState s (ii:.:RiTirI l) (ee:.()) )
    . termStream ts cs us is
    . staticCheck (i>j)
  {-# Inline termStream #-}


instance TermStaticVar Epsilon (TreeIxR p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ i = i
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}


--deletion

instance
  ( TmkCtx1 m ls Deletion (TreeIxR p v a t)
  ) => MkStream m (ls :!: Deletion) (TreeIxR p v a t) where
  mkStream (ls :!: Deletion) sv us is
    = map (\(ss,ee,ii) -> ElmDeletion ii ss)
    . addTermStream1 Deletion sv us is
    $ mkStream ls (termStaticVar Deletion sv is) us (termStreamIndex Deletion sv is)
  {-# Inline mkStream #-}


instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a I)
  ) => TermStream m (TermSymbol ts Deletion) s (is:.TreeIxR p v a I) where
  termStream (ts:|Deletion) (cs:.IVariable ()) (us:.u) (is:.TreeIxR frst i j)
    = map (\(TState s ii ee) ->
              let RiTirI l = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
              in  TState s (ii:.:RiTirI l) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}


instance TermStaticVar Deletion (TreeIxR p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ i = i
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}


-- Invisible starting symbol

instance (Monad m) => MkStream m S (TreeIxR p v a I) where
  mkStream S _ (TreeIxR frst l u) (TreeIxR _ i j)
    = staticCheck (i>=0 && j<=u) . singleton . ElmS $ RiTirI i
  {-# Inline mkStream #-}


instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.TreeIxR p v a I) where
  mkStream S (vs:._) (lus:.TreeIxR frst l u) (is:.TreeIxR _ i j)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiTirI i)
    . staticCheck (i>=0 && j<=u)
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}


--synVar

instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a I) cs c is (TreeIxR p v a I)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxR p v a I) (cs:.c) (is:.TreeIxR p v a I) where
  addIndexDenseGo (cs:._) (vs:.IStatic ()) (us:.TreeIxR frst _ u) (is:.TreeIxR _ _ j)
    = map go . addIndexDenseGo cs vs us is
    where
      go (SvS s tt ii) =
        let RiTirI l' = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
            l         = if l' > j then u+1 else l'
        in traceShow ("S"::String,l,j) $ SvS s (tt:.TreeIxR frst l j) (ii:.:RiTirI (j+1))
  addIndexDenseGo (cs:._) (vs:.IVariable ()) (us:.TreeIxR frst _ u) (is:.TreeIxR _ _ j)
    = map go . addIndexDenseGo cs vs us is
    where
      go (SvS s tt ii) =
        let RiTirI k  = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
            l'        = (rsib frst `VU.unsafeIndex` k) - 1
            l         = if (k < VU.length (rsib frst)) && l' >= 0 then l' else u+1
        in traceShow ("V"::String,rsib frst,k,l) $ SvS s (tt:.TreeIxR frst k l) (ii:.:RiTirI (l+1))
  {-# Inline addIndexDenseGo #-}


instance (MinSize c) => TableStaticVar u c (TreeIxR p v a I) where 
  tableStaticVar _ _ _ _ = IVariable ()
  tableStreamIndex _ c _ (TreeIxR f i j) = TreeIxR f i (j- minSize c)
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}
