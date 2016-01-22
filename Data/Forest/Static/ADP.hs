
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

instance Show (TreeIxR p v a t) where
  show (TreeIxR _ i j) = show (i,j)

minIx, maxIx :: Forest p v a -> TreeIxR p v a t
minIx f = TreeIxR f 0 0

maxIx f = TreeIxR f 0 (VU.length (parent f))
{-# Inline minIx #-}
{-# Inline maxIx #-}

data TF = T | F
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
  linearIndex (TreeIxR _ l _) (TreeIxR _ _ u) (TreeIxR _ i j)
    = let k = if i==j then u else i
      in  linearIndex (Z:.l:.T) (Z:.u:.F) (Z:.k:.(if u==j then F else T))
  {-# Inline linearIndex #-}
  smallestLinearIndex _ = error "still needed?"
  {-# Inline smallestLinearIndex #-}
  largestLinearIndex (TreeIxR p _ u) = largestLinearIndex (Z:.u:.F) --  (VU.length (parent p) +1)*2
  {-# Inline largestLinearIndex #-}
  --size _ (TreeIxR p _ _) = (VU.length (parent p) +1)*2 + 1 -- epsilon mapping
  size (TreeIxR _ l _) (TreeIxR _ _ u) = size (Z:.l:.T) (Z:.u:.F)
  {-# Inline size #-}
  inBounds _ (TreeIxR p _ _) (TreeIxR _ l r) = 0 <= l && r <= VU.length (parent p)
  {-# Inline inBounds #-}


instance IndexStream z => IndexStream (z:.TreeIxR p v a I) where
  streamUp   (ls:.TreeIxR p lf _) (hs:.TreeIxR _ _ ht) = flatten (streamUpMk   ht) (streamUpStep   p lf ht) $ streamUp ls hs
  streamDown (ls:.TreeIxR p lf _) (hs:.TreeIxR _ _ ht) = flatten (streamDownMk lf) (streamDownStep p lf ht) $ streamDown ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}

streamUpMk ht z = return (z,ht,T)
{-# Inline [0] streamUpMk #-}

streamUpStep p lf ht (z,k,tf)
  | k < lf    = return $ SM.Done
  | tf == T   = return $ SM.Yield (z:.TreeIxR p k r') (z,k,F)
  | otherwise = return $ SM.Yield (z:.TreeIxR p k ht) (z,k-1,T)
  where r = rsib p VG.!k
        r' = if k== ht || r == -1 then ht else r
{-# Inline [0] streamUpStep #-}

streamDownMk lf z = return (z,lf,F)
{-# Inline [0] streamDownMk #-}

streamDownStep p lf ht (z,k,tf)
  | k > ht    = return $ SM.Done
  | tf == F   = return $ SM.Yield (z:.TreeIxR p k ht) (z,k,T)
  | otherwise = return $ SM.Yield (z:.TreeIxR p k r') (z,k+1,F)
  where r = rsib p VG.!k
        r' = if k==ht || r == -1 then ht else r
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
node = Node (VG.!)
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
  termStream (ts:|Node f xs) (cs:.IVariable ()) (us:.TreeIxR _ _ u) (is:.TreeIxR frst i j)
    = map (\(TState s ii ee) ->
              let RiTirI l tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                  l' = if VG.length (children frst VG.! l) == 0 then u else l+1
              in  traceShow (i,j,l') $ TState s (ii:.:RiTirI l' F) (ee:.f xs l) )
    . termStream ts cs us is
    . staticCheck (i<j)
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
              let RiTirI l tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
              in  TState s (ii:.:RiTirI l tf) (ee:.()) )
    . termStream ts cs us is
    . staticCheck (i>=j)
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
              let RiTirI l tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
              in  TState s (ii:.:RiTirI l tf) (ee:.()) )
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
    = staticCheck (i>=0 && j<=u) . singleton . ElmS $ RiTirI i (if j==u then F else T)
  {-# Inline mkStream #-}


instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.TreeIxR p v a I) where
  mkStream S (vs:._) (lus:.TreeIxR frst l u) (is:.TreeIxR _ i j)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiTirI i (if j==u then F else T))
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
        let RiTirI l tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
            r | tf == F = u
              | tf == T = rbdef (l+1) frst l
        in traceShow ("S~"::String,u,l,r,j) $ SvS s (tt:.TreeIxR frst l r) (ii:.:RiTirI r tf)
  addIndexDenseGo (cs:._) (vs:.IVariable ()) (us:.TreeIxR frst _ u) (is:.TreeIxR _ _ j)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS = return $ Just $ Left svS
          step Nothing = return $ Done
          step (Just (Left svS@(SvS s tt ii))) = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                                                    traceShow ("T0~"::String,u,k,k) $ return $ Yield (SvS s (tt:.TreeIxR frst k k) (ii:.:RiTirI k F)) (Just (Right svS))
          step (Just (Right (SvS s tt ii))) = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                                                     l         = rbdef (k+1) frst k
                                                 traceShow ("T1~"::String,u,k,l) $ return $ Yield (SvS s (tt:.TreeIxR frst k l) (ii:.:RiTirI l F)) Nothing
          {-# Inline [0] mk #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}



instance (MinSize c) => TableStaticVar u c (TreeIxR p v a I) where 
  tableStaticVar _ _ _ _ = IVariable ()
  tableStreamIndex _ c _ (TreeIxR f i j)
--    | k >= 0 = TreeIxR f i k
    | otherwise = TreeIxR f i j
    where k = getrbound f i -- rsib f VG.! i
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}

getrbound frst k
  | VG.length rs >= k = VG.length rs
  | r < 0             = VG.length rs
  | otherwise         = r
  where rs = rsib frst ; r = rs VG.! k
{-# Inline getrbound #-}

rbdef d frst k = maybe d (\z -> if z<0 then d else z) $ rsib frst VG.!? k
{-# Inline rbdef #-}
