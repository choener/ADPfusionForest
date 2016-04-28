
-- | Data structures and instances to combine efficient 'Forest' structures
-- with @ADPfusion@.

module Data.Forest.Static.AlignRL where

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

import           ADP.Fusion
import           ADP.Fusion.SynVar.Indices
import           Data.Forest.Static
import           Data.PrimitiveArray hiding (map)

import           Data.Forest.Static.Node



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



-- Node: parse a local root

instance
  ( TmkCtx1 m ls (Node r x) (TreeIxR p v a t)
  ) => MkStream m (ls :!: Node r x) (TreeIxR p v a t) where
  mkStream (ls :!: Node f xs) sv us is
    = map (\(ss,ee,ii) -> ElmNode ee ii ss)
    . addTermStream1 (Node f xs) sv us is
    $ mkStream ls (termStaticVar (Node f xs) sv is) us (termStreamIndex (Node f xs) sv is)
  {-# Inline mkStream #-}

-- |
--
-- X    -> n    Y
-- i,T  -> i,T  (i+1),t    -- @t@ = if @i@ has no children, then @E@, else @F@.

instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a I)
  ) => TermStream m (TermSymbol ts (Node r x)) s (is:.TreeIxR p v a I) where
  termStream (ts:|Node f xs) (cs:.IVariable ()) (us:.TreeIxR _ u ut) (is:.TreeIxR frst i it)
    = map (\(TState s ii ee) ->
              let RiTirI l tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                  l'  = l+1
                  tf'  = if VG.null (children frst VG.! l) then E else F
              in  {- traceShow ("N"::String,l,tf) $ -} TState s (ii:.:RiTirI l' tf') (ee:.f xs l) )
    . termStream ts cs us is
    . staticCheck (i<u && it == T)
  {-# Inline termStream #-}


instance TermStaticVar (Node r x) (TreeIxR p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (TreeIxR frst i j) = TreeIxR frst i j
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}


-- | Epsilon
--
-- X    -> ε
-- i,E     i,E    ∀ i

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
    . staticCheck ( (ii==E) || (u==0 && uu==F) ) -- 2nd condition takes care of empty inputs
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

-- | Syntactic variables. Different variants on parsing.
--
-- In case we have @X -> Y@, no restrictions are placed.
--
-- We now need @X -> Y Z@:
--
-- @
--
-- X    ->  Y     Z
-- i,E      i,E   i,E
--
--
--
-- X    ->  Y     Z       we do not split off the first tree
-- i,F      i,E   i,F
--
-- X    ->  Y     Z
-- i,F      i,T   k,F     k,E, if k==u ; 1st tree split off
--          i_k
--
-- X    ->  Y     Z       move complete forest down
-- i,F      i,F   u,E
--
--
--
-- When does this happen? If you have @T -> - F@ then @F@ will now actually
-- be such a @T@.
--
-- X    ->  Y     Z       do not hand i,T down
-- i,T      i,E   i,T
--
-- X    ->  Y     Z       further hand down
-- i,T      i,T   k,E
--          i_k
--
-- @

instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a I) cs c is (TreeIxR p v a I)
  , MinSize c
--  , Show a, VG.Vector v a -- TEMP!
--  , a ~ Info
  ) => AddIndexDense s (us:.TreeIxR p v a I) (cs:.c) (is:.TreeIxR p v a I) where
  addIndexDenseGo (cs:._) (vs:.IStatic ()) (us:.TreeIxR frst u v) (is:.TreeIxR _ j _)
    = map go . addIndexDenseGo cs vs us is
    where
      go (SvS s tt ii) =
        let RiTirI l tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
            tf'         = if l==u then E else tf
        in -- tSI (glb) ('S',u,l,tf,'.',distance $ F.label frst VG.! 0) $
            SvS s (tt:.TreeIxR frst l tf') (ii:.:RiTirI u E)
  addIndexDenseGo (cs:._) (vs:.IVariable ()) (us:.TreeIxR frst u v) (is:.TreeIxR _ j jj)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS = return $ EpsFull jj svS
          step Finis = return $ Done
          -- nothing here
          step (EpsFull E svS@(SvS s tt ii)) = return $ Yield (SvS s (tt:.TreeIxR frst j E) (ii:.:RiTirI j E)) Finis
          -- _ -> TF , for forests: with T having size ε, F having full size
          step (EpsFull F svS@(SvS s tt ii))
            = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                 --tSI (glb) ('V',u,k,F,'.',distance $ F.label frst VG.! 0) .
                 return $ Yield (SvS s (tt:.TreeIxR frst k E) (ii:.:RiTirI k F)) (FullEpsFF svS)  -- @k Epsilon / full@
          -- _ -> TF, for forests: with T having full size, F having size ε
          step (FullEpsFF svS@(SvS s tt ii))
            = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                 --tSI (glb) ('W',u,k,T,'.',distance $ F.label frst VG.! 0) .
                 return $ Yield (SvS s (tt:.TreeIxR frst k F) (ii:.:RiTirI u E)) (OneRemFT svS)   -- @full / u Epsilon@
          -- _ -> TF for forests: with T having size 1, F having full - 1 size
          step (OneRemFT (SvS s tt ii))
            = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                     l         = rbdef u frst k
                     ltf       = if l==u then E else F
                 --tSI (glb) ('W',u,k,l,T,'.',distance $ F.label frst VG.! 0) .
                 return $ Yield (SvS s (tt:.TreeIxR frst k T) (ii:.:RiTirI l ltf)) Finis -- @1 / l ltf@
          -- _ -> TF , for trees: with T having size ε, F having size 1 (or T)
          step (EpsFull T svS@(SvS s tt ii))
            = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                 --tSI (glb) ('V',u,k,F,'.',distance $ F.label frst VG.! 0) .
                 return $ Yield (SvS s (tt:.TreeIxR frst k E) (ii:.:RiTirI k T)) (OneEpsTT svS)
          -- _ -> TF, for trees: with T having size 1, F having size ε
          step (OneEpsTT (SvS s tt ii))
            = do let RiTirI k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                     l         = rbdef u frst k
                 --tSI (glb) ('W',u,k,l,T,'.',distance $ F.label frst VG.! 0) .
                 return $ Yield (SvS s (tt:.TreeIxR frst k T) (ii:.:RiTirI l E)) Finis
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

-- | The next right sibling.

rbdef d frst k = maybe d (\z -> if z<0 then d else z) $ rsib frst VG.!? k
{-# Inline rbdef #-}

-- | Give us the parent for node @k@ or @-1@ if there is no parent

pardef frst k = maybe (-1) id $ parent frst VG.!? k
{-# Inline pardef #-}



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



-- Node

-- | We are a @F@orest at position @i@. Now we request the parent, who
-- happens to be the root of a @T@ree.
--
-- TODO we should actually move the outside index via the @OFirstLeft@
-- (etc) encoding
--
-- X    -> n    Y
-- i,T  -> i,T  i+1,t     -- @t@ = if @i@ has no children, then @E@, else @F@.
--
-- Y'     ->  n       X'
-- i+1,t      i,T     i,T   -- @t@ = if @i@ ...
--
-- Y'     ->  n       X'
-- i,t        i-1,T   i-1,T -- @t@ = if @i-1@ has no children, then @E@ else @F@

instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a O)
  , Show r
  ) => TermStream m (TermSymbol ts (Node r x)) s (is:.TreeIxR p v a O) where
  termStream (ts:|Node f xs) (cs:.OFirstLeft ()) (us:.TreeIxR _ u ut) (is:.TreeIxR frst i it)
    = map (\(TState s ii ee) ->
              let RiTirO li tfi lo tfo = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
                  l' = li - 1
              in  TState s (ii:.:RiTirO li T l' T) (ee:.f xs l') ) -- @li@, since we have now just 'eaten' @li -1 , li@
    . termStream ts cs us is
    -- @i>0@ so that we can actually have a parent
    -- @it==E@ in case we @i-1@ has no children; @it==F@ in case @i-1@ has
    -- children.
    . staticCheck (let hc = not $ VG.null (children frst VG.! (i-1))
                   in  i>0 && (not hc && it==E || hc && it==F))
  {-# Inline termStream #-}

instance TermStaticVar (Node r x) (TreeIxR p v a O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (TreeIxR frst i j) = TreeIxR frst i j
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



-- | Epsilon

instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a O)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.TreeIxR p v a O) where
  termStream (ts:|Epsilon) (cs:.OStatic ()) (us:.TreeIxR _ u uu) (is:.TreeIxR frst i ii)
    = map (\(TState s ii ee) ->
              let RiTirO li tfi lo tfo = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
              in  TState s (ii:.:RiTirO li tfi lo tfo) (ee:.()) )
    . termStream ts cs us is
    . staticCheck ((i==0 && ii==F) || (i==0 && u==0 && ii==E))
  {-# Inline termStream #-}


instance TermStaticVar Epsilon (TreeIxR p v a O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ i = i
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



-- | Deletion.
--
-- Has no conditions on when it is acceptable.

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

-- For both, I / O and O / O systems, we need to consider a large number of
-- cases. The general rule @X -> Y Z@ with all variants follows below.
--
--
-- @
--
-- X    ->  Y     Z
-- i,E      i,E   i,E
--
-- Y^   ->  X^    Z
-- i,E      i,E   i,E
--
-- Z^   ->  Y     X^
-- i,E      i,E   i,E
--
--
--
-- X    ->  Y     Z       we do not split off the first tree; down is empty
-- i,F      i,E   i,F
--
-- Y^   ->  X^    Z
-- i,E      i,F   i,F
--
-- Z^   ->  Y     X^
-- i,F      i,E   i,F
--
--
-- X    ->  Y     Z
-- i,F      i,T   k,t     if k==u then E else F ; 1st tree split off
--          i~k
--
-- Y^   ->  X^    Z
-- i,T      i,F   k,t     if k==u then E else F
-- i~k
--
-- Z^   ->  Y     X^
-- u,E      i,T   i,F     ∀ i ;; for all trees [i,u) !
--          i~u
--
-- Z^   ->  Y     X^
-- k,F      i,T   i,F     i is left sibling of k
--          i~k
--
--
-- X    ->  Y     Z       move complete forest down
-- i,F      i,F   u,E
--
-- Y^   ->  X^    Z
-- i,F      i,F   u,E
--
-- Z^   ->  Y     X^      ∀ i ;; for u,E collect all possible splits.
-- u,E      i,F   i,F
--
--
--
-- X    ->  Y     Z       do not hand i,T down
-- i,T      i,E   i,T
--
-- Y^   ->  X^    Z
-- i,E      i,T   i,T
--
-- Z^   ->  Y     X^
-- i,T      i,E   i,T
--
--
--
-- X    ->  Y     Z       further hand down
-- i,T      i,T   k,E
--          i_k
--
-- Y^   ->  X^    Z
-- i,T      i,T   k,E
-- i_k
--
-- Z^   ->  Y     X^
-- k,E      i,T   i,T
--          i_k
--
--
-- @

data OIEFT x
  = OIEFF x Int -- svS , forests starting at @i@
  | OIETT x Int -- svS , parent index for trees with right boundary @j@
  | OIETF x Int -- svS , parent index for trees with right boundary @u@
  | OIEEE x     -- svS
  | OIFEF x     -- svS
  | OIFTF x     -- svS
  | OITET x     -- svS
  | OIFinis

-- | The different cases for @O@ context with @O@ tables.

data OOEFT x -- = OOE TF x | OOF x | OOT TF x | OOFinis
  = OOE x TF  -- svS , all variants of T F E
  | OOFFE x   -- svS
  | OOTF  x   -- svS
  | OOTT  x   -- svS
  | OOFinis

-- In principle, we are missing an extra boolean case on @j==u@ or @j==l,
-- l/=u@ for tree-symbols, i.e. those that bind terminals. However, in
-- these linear languages, there can be only one such symbol per rule. This
-- in turn means they are never in outside mode on the r.h.s. and hence we
-- have no ambiguity problems.

-- synVar: @Table I@ with @Index O@ We only have two options: @X' -> Y' Z@
-- with @Z@ being in @OStatic@ position or @X' -> Y Z'@ with @Y@ being in
-- @OFirstLeft@ position.
--
-- @
--
-- Z^   ->  Y     X^      ∀ i ;; for u,E collect all possible splits.
-- u,E      i,F   i,F     this is move complete forest down / inside
--
-- Z^   ->  Y     X^      further hand down
-- k,E      i,T   i,T
--          i_k
--
-- Z^   ->  Y     X^
-- u,E      i,T   i,F     ∀ i ;; for all trees [i,u) !
--          i~u
--
-- Z^   ->  Y     X^
-- i,E      i,E   i,E
--
--
--
-- Z^   ->  Y     X^       we do not split off the first tree; down is empty
-- i,F      i,E   i,F
--
-- Z^   ->  Y     X^
-- k,F      i,T   i,F     ∀ i ;; for all trees [i,k) k/=u !
--          i~k
--
--
--
-- Z^   ->  Y     X^      do not hand i,T down
-- i,T      i,E   i,T
--
-- @

instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a I) cs c is (TreeIxR p v a O)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxR p v a I) (cs:.c) (is:.TreeIxR p v a O) where
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (us:.TreeIxR frst u v) (is:.TreeIxR _ j jj)
    = map go .addIndexDenseGo cs vs us is
    where go (SvS s tt ii) =
            let RiTirO li tfi lo tfo = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
            in  SvS s (tt:.TreeIxR frst li tfi) (ii:.:RiTirO j E lo tfo) -- TODO should set right boundary
  addIndexDenseGo (cs:._) (vs:.OFirstLeft ()) (us:.TreeIxR frst u v) (is:.TreeIxR _ j jj)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS@(SvS s tt ii) =
            let RiTirO li tfi lo tfo = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
            in  return $ case jj of
                  E -> OIEFF svS 0
                  F -> OIFEF svS
                  T -> OITET svS
          step OIFinis = return Done
          -- Z^   ->  Y     X^      ∀ i ;; for u,E collect all possible splits.
          -- u,E      i,F   i,F     this is move complete forest down / inside
          step (OIEFF svS@(SvS s tt ii) k) | j==u && k<u
            = return $ Yield (SvS s (tt:.TreeIxR frst k F) (ii:.:RiTirO u E k F)) (OIEFF svS (k+1))
          step (OIEFF svS _)
            = let pj = maybe (-1) id $ F.lsib frst VG.!? j
              in  return $ Skip $ OIETT svS pj
          -- Z^   ->  Y     X^      further hand down
          -- k,E      i,T   i,T
          --          i_k
          step (OIETT svS@(SvS s tt ii) pj) | j<u && pj>=0
            = let pj' = pardef frst pj
                  tr  = if j==u then E else F
              in  return $ Yield (SvS s (tt:.TreeIxR frst pj T) (ii:.:RiTirO j tr pj T)) (OIETT svS pj')
          step (OIETT svS _)
            = let pu = pardef frst $ u - 1
              in  return $ Skip $ OIETF svS pu
          -- Z^   ->  Y     X^
          -- u,E      i,T   i,F     ∀ i ;; for all trees [i,u) !
          --          i~u
          step (OIETF svS@(SvS s tt ii) pu) | j==u && pu>=0
            = let pu' = pardef frst pu
              in  return $ Yield (SvS s (tt:.TreeIxR frst pu T) (ii:.:RiTirO u E pu F)) (OIETF svS pu')
          step (OIETF svS _)
            = return $ Skip $ OIEEE svS
          -- Z^   ->  Y     X^
          -- i,E      i,E   i,E
          step (OIEEE svS@(SvS s tt ii))
            = return $ Yield (SvS s (tt:.TreeIxR frst j E) (ii:.:RiTirO j E j E)) OIFinis
          -- Z^   ->  Y     X^       we do not split off the first tree; down is empty
          -- i,F      i,E   i,F
          step (OIFEF svS@(SvS s tt ii))
            = return $ Yield (SvS s (tt:.TreeIxR frst j E) (ii:.:RiTirO j E j F)) (OIFTF svS)
          -- Z^   ->  Y     X^
          -- k,F      i,T   i,F     i is left sibling of k
          --          i~k
          step (OIFTF svS@(SvS s tt ii)) | Just ls <- F.lsib frst VG.!? j, ls >= 0
            = return $ Yield (SvS s (tt:.TreeIxR frst ls T) (ii:.:RiTirO j F ls F)) OIFinis
          step (OIFTF _) = return $ Skip $ OIFinis
          -- Z^   ->  Y     X^      do not hand i,T down
          -- i,T      i,E   i,T
          step (OITET svS@(SvS s tt ii))
            = return $ Yield (SvS s (tt:.TreeIxR frst j E) (ii:.:RiTirO j E j T)) OIFinis
          {-# Inline [0] mk #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

--synVar: @Table O@   with @Index O@
--
-- @
--
-- Y^   ->  X^    Z
-- i,E      i,E   i,E
--
-- Y^   ->  X^    Z       we do not split off the first tree; down is empty
-- i,E      i,F   i,F
--
-- Y^   ->  X^    Z       do not hand i,T down
-- i,E      i,T   i,T
--
--
--
-- Y^   ->  X^    Z
-- i,T      i,F   k,t     if k==u then E else F ; 1st tree split off
-- i_k
--
-- Y^   ->  X^    Z       further hand down ; k,E because @T@
-- i,T      i,T   k,E
-- i_k
--
--
--
-- Y^   ->  X^    Z       move complete forest down
-- i,F      i,F   u,E
--
-- @

instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a O) cs c is (TreeIxR p v a O)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxR p v a O) (cs:.c) (is:.TreeIxR p v a O) where
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (us:.TreeIxR frst u v) (is:.TreeIxR _ j _)
    = map go .addIndexDenseGo cs vs us is
    where go (SvS s tt ii) =
            let RiTirO li tfi lo tfo = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
            in  SvS s (tt:.TreeIxR frst lo tfo) (ii:.:RiTirO li tfi j E) -- TODO should set right boundary
  addIndexDenseGo (cs:._) (vs:.ORightOf ()) (us:.TreeIxR frst u v) (is:.TreeIxR _ j jj)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS = return $ case jj of
                    E -> OOE   svS minBound
                    F -> OOFFE svS
                    T -> OOTF  svS
          -- done
          step OOFinis = return Done
          -- Y^   ->  X^    Z
          -- i,E      i,E   i,E
          --
          -- Y^   ->  X^    Z       we do not split off the first tree; down is empty
          -- i,E      i,F   i,F
          --
          -- Y^   ->  X^    Z       do not hand i,T down
          -- i,E      i,T   i,T
          step (OOE svS@(SvS s tt ii) tf) | tf < maxBound
            = return $ Yield (SvS s (tt:.TreeIxR frst j tf) (ii:.:RiTirO j tf j E)) (OOE svS (succ tf))
          step (OOE svS@(SvS s tt ii) tf) | tf == maxBound
            = return $ Yield (SvS s (tt:.TreeIxR frst j tf) (ii:.:RiTirO j tf j E)) OOFinis
          -- Y^   ->  X^    Z       move complete forest down
          -- i,F      i,F   u,E
          step (OOFFE svS@(SvS s tt ii))
            = return $ Yield (SvS s (tt:.TreeIxR frst j F) (ii:.:RiTirO u E j E)) OOFinis
          -- Y^   ->  X^    Z
          -- i,T      i,F   k,t     if k==u then E else F ; 1st tree split off
          -- i_k
          step (OOTF svS@(SvS s tt ii))
            = let k = rbdef u frst j
                  tf = if k==u then E else F
              in  return $ Yield (SvS s (tt:.TreeIxR frst j F) (ii:.:RiTirO k tf j E)) (OOTT svS)
          -- Y^   ->  X^    Z       further hand down ; k,E because @T@
          -- i,T      i,T   k,E
          -- i_k
          step (OOTT svS@(SvS s tt ii))
            = let k = rbdef u frst j
              in  return $ Yield (SvS s (tt:.TreeIxR frst j T) (ii:.:RiTirO k E j E)) OOFinis
          {-# Inline [0] mk #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

instance (MinSize c) => TableStaticVar (u I) c (TreeIxR p v a O) where 
  tableStaticVar _ _ (OStatic    d) _ = ORightOf d
  tableStaticVar _ _ (ORightOf   d) _ = ORightOf d
  tableStaticVar _ _ (OFirstLeft d) _ = OLeftOf  d
  tableStaticVar _ _ (OLeftOf    d) _ = OLeftOf  d
  tableStreamIndex _ c _ = id
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}

instance (MinSize c) => TableStaticVar (u O) c (TreeIxR p v a O) where 
  tableStaticVar _ _ (OStatic  d) _ = OFirstLeft d
  tableStaticVar _ _ (ORightOf d) _ = OFirstLeft d
  tableStreamIndex _ c _ = id
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}





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



instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a I) cs c is (TreeIxR p v a C)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxR p v a I) (cs:.c) (is:.TreeIxR p v a C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:.TreeIxR frst u v) (is:.TreeIxR _ j _)
    = map go .addIndexDenseGo cs vs us is
    where go (SvS s tt ii) =
            let RiTirC k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a C))
            in  SvS s (tt:.TreeIxR frst k tf) (ii:.:RiTirC k tf)

instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a O) cs c is (TreeIxR p v a C)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxR p v a O) (cs:.c) (is:.TreeIxR p v a C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:.TreeIxR frst u v) (is:.TreeIxR _ j _)
    = map go .addIndexDenseGo cs vs us is
    where go (SvS s tt ii) =
            let RiTirC k tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a C))
            in  SvS s (tt:.TreeIxR frst k tf) (ii:.:RiTirC k tf)
