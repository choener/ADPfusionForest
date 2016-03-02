
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
import qualified Data.Forest.Static as F
import Biobase.Newick

import           Data.Forest.Static
import           Data.Forest.Static.Node
import           ADP.Fusion
import           Data.PrimitiveArray hiding (map)
import           ADP.Fusion.SynVar.Indices


data TreeIxR p v a t = TreeIxR !(Forest p v a) !Int !TF

instance Show (TreeIxR p v a t) where
  show (TreeIxR _ i j) = show (i,j)

minIx, maxIx :: Forest p v a -> TreeIxR p v a t
minIx f = TreeIxR f 0 minBound

maxIx f = TreeIxR f (VU.length (parent f)) maxBound
{-# Inline minIx #-}
{-# Inline maxIx #-}

data TF = F | T
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
    = 2 * k + fromEnum tf
  {-# Inline linearIndex #-}
  smallestLinearIndex _ = error "still needed?"
  {-# Inline smallestLinearIndex #-}
  largestLinearIndex (TreeIxR p u ut) = 2 * u + 1
  {-# Inline largestLinearIndex #-}
  size (TreeIxR _ l ll) (TreeIxR _ u uu) = 2 * (u+1)
  {-# Inline size #-}
  inBounds (TreeIxR _ l _) (TreeIxR _ u _) (TreeIxR _ k _) = l <= k && k <= u
  {-# Inline inBounds #-}


instance IndexStream z => IndexStream (z:.TreeIxR p v a I) where
  streamUp   (ls:.TreeIxR p lf _) (hs:.TreeIxR _ ht _) = flatten (streamUpMk   ht) (streamUpStep   p lf ht) $ streamUp ls hs
  streamDown (ls:.TreeIxR p lf _) (hs:.TreeIxR _ ht _) = flatten (streamDownMk lf) (streamDownStep p lf ht) $ streamDown ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}

streamUpMk ht z = return (z,ht,T)
{-# Inline [0] streamUpMk #-}

streamUpStep p lf ht (z,k,tf)
  | k < lf    = return $ SM.Done
  | tf == T   = return $ SM.Yield (z:.TreeIxR p k tf) (z,k,F)
  | otherwise = return $ SM.Yield (z:.TreeIxR p k tf) (z,k-1,T)
{-# Inline [0] streamUpStep #-}

streamDownMk lf z = return (z,lf,F)
{-# Inline [0] streamDownMk #-}

streamDownStep p lf ht (z,k,tf)
  | k > ht    = return $ SM.Done
  | tf == F   = return $ SM.Yield (z:.TreeIxR p k F) (z,k,T)
  | otherwise = return $ SM.Yield (z:.TreeIxR p k T) (z,k+1,F)
{-# Inline [0] streamDownStep #-}


instance IndexStream (Z:.TreeIxR p v a t) => IndexStream (TreeIxR p v a t)

instance RuleContext (TreeIxR p v a I) where
  type Context (TreeIxR p v a I) = InsideContext ()
  initialContext _ = IStatic ()
  {-# Inline initialContext #-}



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
  termStream (ts:|Node f xs) (cs:.IVariable ()) (us:.TreeIxR _ u ut) (is:.TreeIxR frst i it)
    = map (\(TState s ii ee) ->
              let RiTirI l tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                  l' = if VG.null (children frst VG.! l) then u else l+1
              in  {- traceShow ("N"::String,l,tf) $ -} TState s (ii:.:RiTirI l' F) (ee:.f xs l) )
    . termStream ts cs us is
    . staticCheck (i<u && it == T)
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
  termStream (ts:|Epsilon) (cs:.IStatic ()) (us:.TreeIxR _ u uu) (is:.TreeIxR frst i ii)
    = map (\(TState s ii ee) ->
              let RiTirI l tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
              in  TState s (ii:.:RiTirI l tf) (ee:.()) )
    . termStream ts cs us is
    . staticCheck (i==u)
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
  termStream (ts:|Deletion) (cs:.IVariable ()) (us:.u) (is:.TreeIxR frst i ii)
    = map (\(TState s ii ee) ->
              let RiTirI l tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
              in  {- traceShow ("-"::String,l,tf) $ -} TState s (ii:.:RiTirI l tf) (ee:.()) )
    . termStream ts cs us is
--    . staticCheck (ii == T)
  {-# Inline termStream #-}


instance TermStaticVar Deletion (TreeIxR p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ i = i
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}


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

-- | When choosing tree and forest sizes, 

data TFsize s
  -- The tree shall have size epsilon, the forest be full. If @TF@ is @F@
  -- then the forest is a real forest, if @TF@ is @T@ then the forest is
  -- a tree.
  = EpsFull TF s
  -- | The tree is full (and actually a forest), the remainder of the
  -- forest is epsilon. This means that in the "tree" synvar, we can only
  -- do indels.
  | FullEpsFF s
  -- | The tree is set, the remaining forest gets what is left.
  | OneRemFT s
  -- | The tree is set, the remaining forest is empty.
  | OneEpsTT s
  | Finis

--synVar

instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a I) cs c is (TreeIxR p v a I)
  , MinSize c
  , Show a, VG.Vector v a -- TEMP!
  , a ~ Info
  ) => AddIndexDense s (us:.TreeIxR p v a I) (cs:.c) (is:.TreeIxR p v a I) where
  addIndexDenseGo (cs:._) (vs:.IStatic ()) (us:.TreeIxR frst u v) (is:.TreeIxR _ j _)
    = map go . addIndexDenseGo cs vs us is
    where
      go (SvS s tt ii) =
        let RiTirI l tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
        in tSI (glb) ('S',u,l,tf,'.',distance $ F.label frst VG.! 0) $ SvS s (tt:.TreeIxR frst (min l u) tf) (ii:.:RiTirI u F)
  addIndexDenseGo (cs:._) (vs:.IVariable ()) (us:.TreeIxR frst u v) (is:.TreeIxR _ j jj)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS = return $ EpsFull jj svS
          step Finis = return $ Done
          -- _ -> TF , for forests: with T having size ε, F having full size
          step (EpsFull F svS@(SvS s tt ii))
            = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                 tSI (glb) ('V',u,k,F,'.',distance $ F.label frst VG.! 0) .
                   return $ Yield (SvS s (tt:.TreeIxR frst u F) (ii:.:RiTirI k F)) (FullEpsFF svS)
          -- _ -> TF, for forests: with T having full size, F having size ε
          step (FullEpsFF svS@(SvS s tt ii))
            = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                 tSI (glb) ('W',u,k,T,'.',distance $ F.label frst VG.! 0) .
                   return $ Yield (SvS s (tt:.TreeIxR frst k F) (ii:.:RiTirI u F)) (OneRemFT svS)
          -- _ -> TF for forests: with T having size 1, F having full - 1 size
          step (OneRemFT (SvS s tt ii))
            = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                     l         = rbdef u frst k
                 tSI (glb) ('W',u,k,l,T,'.',distance $ F.label frst VG.! 0) .
                   return $ Yield (SvS s (tt:.TreeIxR frst k T) (ii:.:RiTirI l F)) Finis
          -- _ -> TF , for trees: with T having size ε, F having size 1 (or T)
          step (EpsFull T svS@(SvS s tt ii))
            = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                 tSI (glb) ('V',u,k,F,'.',distance $ F.label frst VG.! 0) .
                   return $ Yield (SvS s (tt:.TreeIxR frst u F) (ii:.:RiTirI k T)) (OneEpsTT svS)
          -- _ -> TF, for trees: with T having size 1, F having size ε
          step (OneEpsTT (SvS s tt ii))
            = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                     l         = rbdef u frst k
                 tSI (glb) ('W',u,k,l,T,'.',distance $ F.label frst VG.! 0) .
                   return $ Yield (SvS s (tt:.TreeIxR frst k T) (ii:.:RiTirI u F)) Finis
          {-# Inline [0] mk #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

glb = False

tSI cond s i = if cond then traceShow s i else i

instance (MinSize c) => TableStaticVar u c (TreeIxR p v a I) where 
  tableStaticVar _ _ _ _ = IVariable ()
  tableStreamIndex _ c _ = id
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}

getrbound frst k
  | VG.length rs >= k = VG.length rs
  | r < 0             = VG.length rs
  | otherwise         = r
  where rs = rsib frst ; r = rs VG.! k
{-# Inline getrbound #-}

trright frst k = rbdef (VG.length $ rsib frst) frst k

rbdef d frst k = maybe d (\z -> if z<0 then d else z) $ rsib frst VG.!? k
{-# Inline rbdef #-}



-- * Outside instances

-- | Outside running index structure requires two local index structures.
-- One is for the inside symbols, one for the outside symbol.

data instance RunningIndex (TreeIxR p v a O) = RiTirO !Int !TF !Int !TF -- I, I, O, O

-- | Outside works in the opposite direction.
--
-- TODO check if the original @Up@ / @Down@ combination is ok.

instance IndexStream z => IndexStream (z:.TreeIxR p v a O) where
  streamUp   (ls:.TreeIxR p lf _) (hs:.TreeIxR _ ht _) = flatten (streamDownMk ht) (streamDownStep p lf ht) $ streamUp ls hs
  streamDown (ls:.TreeIxR p lf _) (hs:.TreeIxR _ ht _) = flatten (streamUpMk   lf) (streamUpStep   p lf ht) $ streamDown ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}

instance RuleContext (TreeIxR p v a O) where
  type Context (TreeIxR p v a O) = OutsideContext ()
  initialContext _ = OStatic ()
  {-# Inline initialContext #-}



-- Node

-- | We are a @F@orest at position @i@. Now we request the parent, who
-- happens to be the root of a @T@ree.

instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a O)
  ) => TermStream m (TermSymbol ts (Node r x)) s (is:.TreeIxR p v a O) where
  termStream (ts:|Node f xs) (cs:.OFirstLeft ()) (us:.TreeIxR _ u ut) (is:.TreeIxR frst i it)
    = map (\(TState s ii ee) ->
              let RiTirO li tfi lo tfo = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
                  l' = parent frst VG.! i
              in  TState s (ii:.:RiTirO l' T lo tfo) (ee:.f xs l') )
    . termStream ts cs us is
    . staticCheck (i<u && i>0 && parent frst VG.! i >= 0 && it == F)
  {-# Inline termStream #-}

instance TermStaticVar (Node r x) (TreeIxR p v a O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (TreeIxR frst i j) = TreeIxR frst i j
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



-- Deletion

instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a O)
  ) => TermStream m (TermSymbol ts Deletion) s (is:.TreeIxR p v a O) where
  termStream (ts:|Deletion) (cs:._) (us:.u) (is:.TreeIxR frst i ii)
    = map (\(TState s ii ee) ->
              let RiTirO li tfi lo tfo = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
              in  TState s (ii:.:RiTirO li tfi lo tfo) (ee:.()) )
    . termStream ts cs us is
  {-# Inline termStream #-}


instance TermStaticVar Deletion (TreeIxR p v a O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ i = i
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



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



-- In principle, we are missing an extra boolean case on @j==u@ or @j==l,
-- l/=u@ for tree-symbols, i.e. those that bind terminals. However, in
-- these linear languages, there can be only one such symbol per rule. This
-- in turn means they are never in outside mode on the r.h.s. and hence we
-- have no ambiguity problems.

-- synVar: @Table I@ with @Index O@ We only have two options: @X' -> Y' Z@
-- with @Z@ being in @OStatic@ position or @X' -> Y Z'@ with @Y@ being in
-- @OFirstLeft@ position.

instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a I) cs c is (TreeIxR p v a O)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxR p v a I) (cs:.c) (is:.TreeIxR p v a O) where
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (us:.TreeIxR frst u v) (is:.TreeIxR _ _ _)
    = undefined
  addIndexDenseGo (cs:._) (vs:.OFirstLeft ()) (us:.TreeIxR frst u v) (is:.TreeIxR _ _ _)
    = undefined

--synVar: @Table I@   with @Index O@

instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a O) cs c is (TreeIxR p v a O)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxR p v a O) (cs:.c) (is:.TreeIxR p v a O) where
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (us:.TreeIxR frst u v) (is:.TreeIxR _ j _)
    = undefined


