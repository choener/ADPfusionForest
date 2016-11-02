
-- | Data structures and instances to combine efficient 'Forest' structures
-- with @ADPfusion@.

module ADP.Fusion.Core.ForestAlign.PermuteRightLinear where

import qualified Data.List as L
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
import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import           Data.Vector.Instances
import qualified Data.Vector.Algorithms.Intro as VI
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S
import           Data.List (subsequences, permutations)
import qualified Data.List as L
import qualified Prelude as P

import           ADP.Fusion.Core
import           Data.Forest.Static
import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Term.Node.Type

-- HETEROGEN

-- |

data TreeIxR p v a t
  -- | The @TreeIxR@ constructor holds the runtime information for the
  -- current subforest we look at.
  --
  -- We have a pointer to the actual forest structure @Forest p v a@. Next,
  -- we have @Lookup@, it gives a linear index from the set of ordered
  -- subforests to the set @|N@.
  --
  -- The actual runtime position is held by @TFE@, which is an index
  -- structure in the current substructure.
  = TreeIxR !(Forest p v a) !LookUp !TFE

instance Show (TreeIxR p v a t) where
  show (TreeIxR _ i j) = show (i,j)

minIx, maxIx :: Forest Pre v a -> TreeIxR Pre v a t
minIx f = let l = mkLookUp f
          in  TreeIxR f l (F (VU.fromList []))  -- $ roots f)

maxIx f = let l = mkLookUp f
          in  TreeIxR f l (E $ VU.length (parent f))
{-# Inline minIx #-}
{-# Inline maxIx #-}

-- | For permutated trees, we need to know the order of the remaining
-- children, given as a @VU.Vector Int@, yielding the next linearized
-- index. The @LookUp@ data structure holds all possible such orderings of
-- children.

type LookUp = HM.HashMap (VU.Vector Int) Int

-- | Given a static forest, we need to associate each possible ordered
-- subset of children of each node with a linear index. The @mkLookUp@
-- function generates this.
--
-- TODO use 'sortedSubForests' such that the partial order matches the
-- linearized order.

mkLookUp :: Forest Pre v a -> LookUp
mkLookUp f = HM.fromList . flip P.zip [0..] $ sortedSubForests f
{-
mkLookUp f = HM.fromList . flip P.zip [0..] . go $ roots f : (VG.toList $ children f)
  where go :: [VU.Vector Int] -> [VU.Vector Int]
        go = P.map VG.fromList
           . S.toList . S.fromList
           . P.concatMap (P.tail . subsequences)
           . P.concatMap permutations
           . P.map VG.toList
        -- @go@ generates all permutations (i.e. all orders of children),
        -- then for each such order provides all possible subsequences.
        -- This yields all ordered subsets. These are then made unique and
        -- associated in the main body with linearized indices.
-}

-- | @TFE@ provides the three possible "states" of our system. @E@
-- indicates that we have reached an indixed epsilon state. @T@ is the tree
-- originating at a particular node. Finally @F@ is the subforest with an
-- attached ordered set of subtrees.

data TFE
  -- | Forest with permutation. The vector holds the trees making up the
  -- forest, and their order via the root node indices of the individual
  -- trees.
  --
  -- TODO do we allow empty forests?
  = F (VU.Vector Int)
  -- | A single tree, represented by the index of the root node.
  | T !Int
  -- | An empty forest, BUT annotated with index for the subforest "to the
  -- right of it".
  | E !Int
  deriving (Show,Eq,Ord)

isTree (T _) = True
isTree _     = False
{-# Inline isTree #-}

isEmpty (E _) = True
isEmpty _ = False
{-# Inline isEmpty #-}

getTFEIx (T l) = l
getTFEIx (E l) = l
getTFEIx (F vs)
  | VU.null vs = error "AlignPermuteRL: Forest empty" -- change!!!
  | otherwise = VU.head vs


-- | As usual, we need a running index. We only need the @TFE@ structure,
-- since now (and compared to @AlignRL.hs@) we actually carry the node
-- information in each @TFE@ ctor.

data instance RunningIndex (TreeIxR p v a I) = RiTirI !TFE


-- | The index function needs to provide a linearized representation of the
-- @TFE@-based index.

instance Index (TreeIxR p v a t) where
  -- | trees @T@ are stored in the first line, i.e. @+0@, forests @F@ (with
  -- @j==u@ are stored in the second line, i.e. @+u+1@ to each index.
  -- Finally, all @F@ structures are looked up based on the linear index,
  -- shifted by the base width of @2*m@.
  linearIndex (TreeIxR _ _ ll) (TreeIxR _ _ uu) (TreeIxR _ lk tf)
    | T k <- tf = 2*k
    | E k <- tf = 2*k + 1
    | F k <- tf = 2*(m+1) + HM.lookupDefault (error "AlignPermuteRL: invariant violated!") k lk
    where E m = uu
  {-# Inline linearIndex #-}
  smallestLinearIndex _ = error "still needed?"
  {-# Inline smallestLinearIndex #-}
  largestLinearIndex (TreeIxR p lk (E u)) = 2 * (u+1) + HM.size lk
  largestLinearIndex (TreeIxR p lk err) = error $ "non-legal largest index structure: " P.++ show err
  {-# Inline largestLinearIndex #-}
  size (TreeIxR _ l ll) (TreeIxR _ lk (E u)) = 2 * (u+1) + HM.size l + 1
  {-# Inline size #-}
  inBounds (TreeIxR _ l _) (TreeIxR _ u _) (TreeIxR _ k _) = error "inBounds: write me" -- l <= k && k <= u
  {-# Inline inBounds #-}



instance IndexStream z => IndexStream (z:.TreeIxR Pre v a I) where
  streamUp   (ls:.TreeIxR p llk lf) (hs:.TreeIxR _ _ ht) = flatten (streamUpMk   p lf ht) (streamUpStep   p llk lf ht) $ streamUp ls hs
--  streamDown (ls:.TreeIxR p llk lf) (hs:.TreeIxR _ _ ht) = flatten (streamUpMk   p lf ht) (streamUpStep   p llk lf ht) $ streamDown ls hs -- STUPID!!!
  streamDown (ls:.TreeIxR p llk lf) (hs:.TreeIxR _ _ ht) = flatten (streamDownMk p lf ht) (streamDownStep p llk lf ht) $ streamDown ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}

-- cull from p the non-needed parts via lf ht
streamUpMk p lf ht z =
      -- all sorted subsets of subforests in the forest (have a beer).
  let ssf = sortedSubForests p
      -- extract the highest possible index, which by definition is an
      -- @E index@.
      E ht' = ht
  in  {- trace ("XXX" P.++ show ssf) . -} return $ SE' ht' (z,ssf)
{-# Inline [0] streamUpMk #-}

streamDownMk p lf ht z =
  let ssf = reverse $ VG.empty : sortedSubForests p
  in  return $ Stp (z,ssf)
{-# Inline [0] streamDownMk #-}

-- |

data StepTFE x
  -- | @x@ is a set of size>=1, which will be turned into a forest.
  = SF x
  -- | @x@ is a set of size ==1, which will be turned into a tree.
  | ST x
  -- | Perform one step in @streamUpStep@. In case of trees, this will
  -- actually yield both a tree and a forest.
  | Stp x
  -- | This encodes that we have an empty forest (@E@), but directly
  -- encodes the highest @Int@-index given via @streamUpMk@.
  | SE' Int x
  -- | Only for outside calculations!
  | SEout x

-- | For each index @k@, we can easily first calculate @Epsilon k@. Then we
-- want to know the tree at index @k@, but this needs knowledge of all
-- subforests below it, hence we need to calculate this before @Tree k@.

-- this one is called only once and creates an @E k@ element at the highest
-- possible index.
streamUpStep p lk lf ht (SE' k (z,xs))
  = return $ SM.Yield (z:.TreeIxR p lk (E k)) (Stp (z,xs))
-- there is no subforest left to work with. We are done.
streamUpStep p lk lf ht (Stp (z,[]))
  = return $ SM.Done
-- We have at least one sorted subforest @x:@ to deal with. By definition,
-- sets of size 0 do not happen. This is enforced by @sortedSubForests@
-- which produces vectors of @size >= 1@.
streamUpStep p lk lf ht (Stp (z,x:xs))
  -- subsets of size one are trees. They first create an @E@psilon object.
  -- Then they create a @T@ree object, followed by a @F@orest with one tree.
  | sz == 1 = return $ SM.Yield (z:.TreeIxR p lk (E i)) (ST (z,x:xs))
  -- subsets of size 2 or more just create forests and we jump directly to
  -- forest creation.
  | sz >= 2 = return $ SM.Skip (SF (z,x:xs))
  where sz = VU.length x
        i = VU.head x
-- Here we deal with structures that are supposed to be a tree @T@, via
-- @ST@. Seems stupid at first, but if the set size of @x@ is one, we first
-- create a @T@ree @T i@, then we will produce a forest @F [i]@ one step
-- later.
-- Here, we only have subsets of size ==1. We build a tree (we have already
-- built the @E@ part before), and continue on to build a forest with
-- exactly one tree inside.
streamUpStep p lk lf ht (ST (z,x:xs))
  = return $ SM.Yield (z:.TreeIxR p lk (T i)) (SF (z,x:xs))
  where i = VU.head x
-- Create an ordered subforest @F x@. After that, we are done with @x@
-- (indepedent of it being a tree or a forest), and continue with the
-- remainder of the sets.
streamUpStep p lk lf ht (SF (z,x:xs))
  = return $ SM.Yield (z:.TreeIxR p lk (F x)) (Stp (z,xs))
{-# Inline [0] streamUpStep #-}

-- |

-- this is the case of our artificially added size==0 set.
streamDownStep p lk lf ht (Stp (z,[x]))
  = let E k = ht
    in  return $ SM.Yield (z:.TreeIxR p lk (E k)) (Stp (z,[]))
streamDownStep p lk lf ht (Stp (z,[]))
  = return $ SM.Done
streamDownStep p lk lf ht (Stp (z,x:xs))
  | sz == 1 = return $ SM.Yield (z:.TreeIxR p lk (F x)) (ST (z,x:xs))
  | sz >= 2 = return $ SM.Yield (z:.TreeIxR p lk (F x)) (Stp (z,xs))
  where sz = VG.length x
streamDownStep p lk lf ht (ST (z,x:xs))
  = return $ SM.Yield (z:.TreeIxR p lk (T i)) (SEout (z,x:xs))
  where i = VG.head x
streamDownStep p lk lf ht (SEout (z,x:xs))
  = return $ SM.Yield (z:.TreeIxR p lk (E i)) (Stp (z,xs))
  where i = VG.head x
{-# Inline [0] streamDownStep #-}

{-

streamDownMk lf ht z = return (z,lf,minBound :: TF)
{-# Inline [0] streamDownMk #-}

streamDownStep p lf ht (z,k,tf)
  | k > ht         = return $ SM.Done
  | tf == maxBound = return $ SM.Yield (z:.TreeIxR p k tf) (z,k+1,minBound)
  | otherwise      = return $ SM.Yield (z:.TreeIxR p k tf) (z,k,succ tf)
{-# Inline [0] streamDownStep #-}

-}

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
  , Show r
  ) => TermStream m (TermSymbol ts (Node r x)) s (is:.TreeIxR p v a I) where
  termStream (ts:|Node f xs) (cs:.IVariable ()) (us:.TreeIxR _ ul utfe) (is:.TreeIxR frst il itfe)
    = map (\(TState s ii ee) ->
              let RiTirI (T l) = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                  cs = children frst VG.! l
                  fe = if VG.null cs then E l else F cs
              in  traceShow ("N"::String,cs,fe, f xs l) $ TState s (ii:.:RiTirI fe) (ee:.f xs l) )
    . termStream ts cs us is
    . staticCheck ({- itfe < utfe && -} isTree itfe)
  {-# Inline termStream #-}


instance TermStaticVar (Node r x) (TreeIxR p v a I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (TreeIxR frst i j) = TreeIxR frst i j
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



-- PermNode: parse a local root and permute the local forest

instance
  ( TmkCtx1 m ls (PermNode r x) (TreeIxR p v a t)
  ) => MkStream m (ls :!: PermNode r x) (TreeIxR p v a t) where
  mkStream (ls :!: PermNode f xs) sv us is
    = map (\(ss,ee,ii) -> ElmPermNode ee ii ss)
    . addTermStream1 (PermNode f xs) sv us is
    $ mkStream ls (termStaticVar (PermNode f xs) sv is) us (termStreamIndex (PermNode f xs) sv is)
  {-# Inline mkStream #-}

-- |
--
-- X    -> n    Y
-- i,T  -> i,T  (i+1),t    -- @t@ = if @i@ has no children, then @E@, else @F@.

instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a I)
  ) => TermStream m (TermSymbol ts (PermNode r x)) s (is:.TreeIxR p v a I) where
  termStream (ts:|PermNode f xs) (cs:.IVariable ()) (us:.TreeIxR _ ul utfe) (is:.TreeIxR frst il itfe)
    = flatten mk step
    . termStream ts cs us is
    . staticCheck ({- itfe < utfe && -} isTree itfe)
    where mk (TState s ii ee) =
            let RiTirI (T l) = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                cs = children frst VG.! l
                fe = if VG.null cs then Nothing else (Just $ permutations $ VU.toList cs)
            in  return (s, ii, ee, fe)
          step (s, _ , _ , Just [])
            = return $ Done
          step (s, ii, ee,  Nothing)
            = let RiTirI (T l) = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
              in  return $ Yield (TState s (ii:.:RiTirI (E l)) (ee:.f xs l)) (s, ii, ee, Just [])
          step (s, ii, ee, Just (y:ys))
            = let RiTirI (T l) = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
              in  return $ Yield (TState s (ii:.:RiTirI (F $ VU.fromList y)) (ee:.f xs l)) (s, ii, ee, Just ys)
  {-# Inline termStream #-}


instance TermStaticVar (PermNode r x) (TreeIxR p v a I) where
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
  termStream (ts:|Epsilon) (cs:.IStatic ()) (us:.TreeIxR _ ul utfe) (is:.TreeIxR frst il itfe)
    = map (\(TState s ii ee) ->
              let RiTirI ef = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                  l         = case ef of {E l -> l ; F _ -> 0}
              in  TState s (ii:.:RiTirI ef) (ee:.()) )
    . termStream ts cs us is
    . staticCheck ( (isEmpty itfe) || getTFEIx utfe == 0) --TODO: 2nd condition takes care of empty inputs
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
              let RiTirI tfe = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
              in  {- traceShow ("-"::String,l,tf) $ -} TState s (ii:.:RiTirI tfe) (ee:.()) )
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
  mkStream S _ (TreeIxR frst ul utfe) (TreeIxR _ kl ktfe)
    = staticCheck ((getTFEIx ktfe) >=0 && (getTFEIx ktfe) <= (getTFEIx utfe)) . singleton . ElmS $ RiTirI ktfe
  {-# Inline mkStream #-}


instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.TreeIxR p v a I) where
  mkStream S (vs:._) (lus:.TreeIxR frst ul utfe) (is:.TreeIxR _ kl ktfe)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiTirI ktfe)
    . staticCheck ((getTFEIx ktfe) >=0 && (getTFEIx ktfe) <= (getTFEIx utfe))
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}

-- | When choosing tree and forest sizes, 

data TFsize s
  -- The tree shall have size epsilon, the forest be full. If @TF@ is @F@
  -- then the forest is a real forest, if @TF@ is @T@ then the forest is
  -- a tree.
  = EpsFull TFE s
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
-- be such a @T@.    T -> TF ; (1) T -> εT ; (2) T -> Tε
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
  addIndexDenseGo (cs:._) (vs:.IStatic ()) (us:.TreeIxR frst ul utfe) (is:.TreeIxR _ jl jtfe)
    = map go . addIndexDenseGo cs vs us is
    where
      go (SvS s tt ii) =
        let RiTirI tfe = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
            -- TODO this will probably barf, because we need the index
            -- "after the empty forest", which we can't get anymore.
            tfe'       = if getTFEIx tfe == getTFEIx utfe then E (getTFEIx tfe) else tfe
        in  tSI (glb) ('S',tfe,'.') $
            SvS s (tt:.TreeIxR frst ul tfe') (ii:.:RiTirI utfe)
  addIndexDenseGo (cs:._) (vs:.IVariable ()) (us:.TreeIxR frst ul utfe) (is:.TreeIxR _ jl jtfe)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS = return $ EpsFull jtfe svS
          step Finis = return $ Done
          -- nothing here
          step (EpsFull (E _) svS@(SvS s tt ii))
            = let j = getTFEIx jtfe
              in  return $ Yield (SvS s (tt:.TreeIxR frst jl (E j)) (ii:.:RiTirI (E j))) Finis
          -- _ -> TF , for forests: with T having size ε, F having full size
          step (EpsFull (F ys) svS@(SvS s tt ii))
            = do let RiTirI ktfe = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                     k           = getTFEIx ktfe
                 tSI (glb) ('V',ktfe) .
                   return $ Yield (SvS s (tt:.TreeIxR frst jl (E k)) (ii:.:RiTirI ktfe)) (FullEpsFF svS)  -- @k Epsilon / full@
          -- _ -> TF, for forests: with T having full size, F having size ε
          step (FullEpsFF svS@(SvS s tt ii))
            = do let RiTirI ktfe = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                     u           = getTFEIx utfe
                 tSI (glb) ('A',ktfe) .
                   return $ Yield (SvS s (tt:.TreeIxR frst jl ktfe) (ii:.:RiTirI (E u))) (OneRemFT svS)   -- @full / u Epsilon@
          -- _ -> TF for forests: with T having size 1, F having full - 1 size
          step (OneRemFT (SvS s tt ii))
            = do let RiTirI (F kcs) = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                     k         = VU.head kcs
                     cs        = VU.tail kcs
                     ltfe      = if VU.null cs then (E $ getTFEIx utfe) else F cs
                 tSI (glb) ('B') .
                   return $ Yield (SvS s (tt:.TreeIxR frst jl (T k)) (ii:.:RiTirI ltfe)) Finis -- @1 / l ltf@
          -- _ -> TF , for trees: with T having size ε, F having size 1 (or T)
          step (EpsFull (T _) svS@(SvS s tt ii))
            = do let RiTirI (T k)  = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                 tSI (glb) ('Q') .
                   return $ Yield (SvS s (tt:.TreeIxR frst ul (E k)) (ii:.:RiTirI (T k))) (OneEpsTT svS)
          -- _ -> TF, for trees: with T having size 1, F having size ε
          step (OneEpsTT (SvS s tt ii))
            = do let RiTirI (T k) = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                     l         = rbdef (getTFEIx utfe) frst k
                 tSI (glb) ('W') .
                   return $ Yield (SvS s (tt:.TreeIxR frst ul (T k)) (ii:.:RiTirI (E l))) Finis
          {-# Inline [0] mk #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

glb = True

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


-- Outside


data instance RunningIndex (TreeIxR p v a O) = RiTirO !TFE



instance IndexStream z => IndexStream (z:.TreeIxR Pre v a O) where
  streamUp   (ls:.TreeIxR p llk lf) (hs:.TreeIxR _ _ ht) = flatten (streamDownMk   p lf ht) (streamDownStep   p llk lf ht) $ streamDown ls hs
  streamDown (ls:.TreeIxR p llk lf) (hs:.TreeIxR _ _ ht) = flatten (streamUpMk p lf ht) (streamUpStep p llk lf ht) $ streamUp ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}



instance RuleContext (TreeIxR p v a O) where
  type Context (TreeIxR p v a O) = OutsideContext ()
  initialContext _ = OStatic ()
  {-# Inline initialContext #-}


-- | Node
--
-- Inside:
-- @
-- M     -> n     F
-- i,T   -> i,T   <ls>,F
--
-- where ls = ordered subforest of all children of 'i'
-- @
--
-- Outside:
-- @
-- F       -> n     M
-- <ls>,F  -> i,T   i,T
-- @
--
-- with the condition that the rule is active only if @<ls>@ is indeed the
-- whole ordered subforest below @i@.

instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a O)
  , Show r
  ) => TermStream m (TermSymbol ts (Node r x)) s (is:.TreeIxR p v a O) where
  termStream (ts:|Node f xs) (cs:.OFirstLeft ()) (us:.TreeIxR _ ul utfe) (is:.TreeIxR frst il itfe)
    = map (\(TState s ii ee) ->
              let RiTirO l = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
                  p = case l of 
                        E i  -> i 
                        F cs -> parent frst VG.! VG.head cs
              in  TState s (ii:.:RiTirO (T p)) (ee:.f xs p) )
    . termStream ts cs us is
    . staticCheck ({- itfe < utfe && -} isOrdfull frst itfe)
  {-# Inline termStream #-}


instance TermStaticVar (Node r x) (TreeIxR p v a O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (TreeIxR frst i j) = TreeIxR frst i j
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



isOrdfull:: (Forest p v a) -> TFE -> Bool 
isOrdfull frst (F cs)
  | Just c <- cs VG.!? 0
  , let p = parent frst VG.! c 
  , p >= 0
  = children frst VG.! p == cs
isOrdfull frst (E i) = VG.null $ children frst VG.! i
isOrdfull _    _     = False
{-# Inline isOrdfull   #-}



-- PermNode

instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a O)
  , Show r
  ) => TermStream m (TermSymbol ts (PermNode r x)) s (is:.TreeIxR p v a O) where
  termStream (ts:|PermNode f xs) (cs:.OFirstLeft ()) (us:.TreeIxR _ ul utfe) (is:.TreeIxR frst il itfe)
    = map (\(TState s ii ee) ->
              let RiTirO l = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
                  p = case l of 
                        E i  -> i 
                        F cs -> parent frst VG.! VG.head cs
              in  TState s (ii:.:RiTirO (T p)) (ee:.f xs p) )
    . termStream ts cs us is
    . staticCheck ({- itfe < utfe && -} isPermfull frst itfe) --instead of isTree ask if it is a full ordered vector of its siblings including itself 
  {-# Inline termStream #-}


instance TermStaticVar (PermNode r x) (TreeIxR p v a O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ (TreeIxR frst i j) = TreeIxR frst i j
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}



isPermfull:: (Forest p v a) -> TFE -> Bool 
isPermfull frst (F cs)
  | Just c <- cs VG.!? 0
  , let p = parent frst VG.! c 
  , p >= 0
  = VG.length (children frst VG.! p) == VG.length cs  -- cs is a subset of the other vector
isPermfull frst (E i) = VG.null $ children frst VG.! i
isPermfull _    _     = False
{-# Inline isPermfull #-}



-- Epsilon


instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a O)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.TreeIxR p v a O) where
  termStream (ts:|Epsilon) (cs:.OStatic ()) (us:.TreeIxR _ ul utfe) (is:.TreeIxR frst il itfe)
    = map (\(TState s ii ee) ->
              let RiTirO ef = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
              in  TState s (ii:.:RiTirO ef) (ee:.()) )
    . termStream ts cs us is
    . staticCheck (case itfe of {F cs -> cs == roots frst; _ -> False}) 
  {-# Inline termStream #-}


instance TermStaticVar Epsilon (TreeIxR p v a O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ i = i
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}





-- |
--
-- das wird deletion
--
-- Inside
-- @
-- T   -> - F
-- i,? ->   i,?


--Deletion


instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a O)
  ) => TermStream m (TermSymbol ts Deletion) s (is:.TreeIxR p v a O) where
  termStream (ts:|Deletion) (cs:._) (us:.u) (is:.TreeIxR frst i ii)
    = map (\(TState s ii ee) ->
              let RiTirO tfe = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
              in  {- traceShow ("-"::String,l,tf) $ -} TState s (ii:.:RiTirO tfe) (ee:.()) )
    . termStream ts cs us is
--    . staticCheck (ii == T)
  {-# Inline termStream #-}


instance TermStaticVar Deletion (TreeIxR p v a O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ i = i
  {-# Inline [0] termStaticVar   #-}
  {-# Inline [0] termStreamIndex #-}


-- Invisible starting symbol

instance (Monad m) => MkStream m S (TreeIxR p v a O) where
  mkStream S _ (TreeIxR frst ul utfe) (TreeIxR _ kl ktfe)
    = staticCheck ((getTFEIx ktfe) >=0 && (getTFEIx ktfe) <= (getTFEIx utfe)) . singleton . ElmS $ RiTirO ktfe
  {-# Inline mkStream #-}


instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.TreeIxR p v a O) where
  mkStream S (vs:._) (lus:.TreeIxR frst ul utfe) (is:.TreeIxR _ kl ktfe)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiTirO ktfe)
    . staticCheck ((getTFEIx ktfe) >=0 && (getTFEIx ktfe) <= (getTFEIx utfe))
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}











-- OOE for E and T

data OOEFT x
  = OOE x !TFE
  | OOEF x [TFE]
  | OOF x !TFE
  | OOFinis




instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a O) cs c is (TreeIxR p v a O)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxR p v a O) (cs:.c) (is:.TreeIxR p v a O) where
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (us:.TreeIxR frst ul utfe) (is:.TreeIxR _ jl jtfe)
    = map go .addIndexDenseGo cs vs us is
    where go (SvS s tt ii) =
            let RiTirO ol = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
            in  SvS s (tt:.TreeIxR frst ul ol) (ii:.:RiTirO ol) -- TODO should set right boundary
  addIndexDenseGo (cs:._) (vs:.ORightOf ()) (us:.TreeIxR frst ul utfe) (is:.TreeIxR _ jl jtfe)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS = return $ case jtfe of
                    E _ -> OOE svS jtfe
                    T _ -> OOE svS jtfe
                    F _ -> OOF svS jtfe
          step OOFinis = return Done
          step (OOE svS@(SvS s tt ii) (E i)) | i < (getTFEIx utfe) = 
            return $ Yield (SvS s (tt:.TreeIxR frst jl (E i)) (ii:.:RiTirO (E i))) (OOE svS (T i))
          step (OOE svS@(SvS s tt ii) (T i)) | i < (getTFEIx utfe) = 
            return $ Yield (SvS s (tt:.TreeIxR frst jl (T i)) (ii:.:RiTirO (T i))) (OOEF svS (genPerm frst i)) 
          step (OOEF svS@(SvS s tt ii) []) = return Done
          step (OOEF svS@(SvS s tt ii) (F i:is)) = 
            return $ Yield (SvS s (tt:.TreeIxR frst jl (F i)) (ii:.:RiTirO (F i))) (OOEF svS is) 
          step (OOF svS@(SvS s tt ii) (F i)) = 
            return $ Yield (SvS s (tt:.TreeIxR frst jl (F i)) (ii:.:RiTirO (E (getTFEIx utfe)))) OOFinis 
          {-# Inline [0] mk #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}



genPerm frst i
  | let p = parent frst VG.! i
  , p >= 0
  , let cs = children frst VG.! p
  = L.map (F. VG.fromList) . L.map (i:) . L.concatMap permutations . subsequences . L.delete i $ VG.toList cs 
genPerm _ _ = []
{-# Inline genPerm #-}




data OIEFT x
  = OIEE x !TFE
  | OIET x !TFE
  | OIEF x [TFE]
  | OIT x !TFE
  | OIFE x !TFE
  | OIFT x !(VU.Vector Int) [Int]
  | OIFinis


instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a I) cs c is (TreeIxR p v a O)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxR p v a I) (cs:.c) (is:.TreeIxR p v a O) where
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (us:.TreeIxR frst ul utfe) (is:.TreeIxR _ jl jtfe)
    = map go .addIndexDenseGo cs vs us is
    where go (SvS s tt ii) =
            let RiTirO lo = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
            in  SvS s (tt:.TreeIxR frst jl lo) (ii:.:RiTirO lo) -- TODO should set right boundary
  addIndexDenseGo (cs:._) (vs:.OFirstLeft ()) (us:.TreeIxR frst ul utfe) (is:.TreeIxR _ jl jtfe)
    = flatten mk step . addIndexDenseGo cs vs us is
    where mk svS@(SvS s tt ii) =
            let RiTirO lo = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a O))
            in  return $ case lo of
                  E _ -> OIEE svS lo
                  F _ -> OIFE svS lo
                  T _ -> OIT svS lo
          step OIFinis = return Done
          step (OIEE svS@(SvS s tt ii) (E i)) | i < (getTFEIx utfe) =
            return $ Yield (SvS s (tt:.TreeIxR frst jl (E i)) (ii:.:RiTirO (E i))) (OIET svS (E i))
          step (OIEE svS@(SvS s tt ii) (E i)) = return $ Skip (OIET svS (E i))
          step (OIET svS@(SvS s tt ii) (E i)) | Just l <- leftSibling (rightMostLeaf frst (getTFEIx utfe)) frst i =
            return $ Yield (SvS s (tt:.TreeIxR frst jl (T l)) (ii:.:RiTirO (T l))) 
                           (OIEF svS $ if i == (getTFEIx utfe) then (L.map F $ sortedSubForests frst) else [])
          step (OIET svS@(SvS s tt ii) (E i)) = return Done
          step (OIEF svS@(SvS s tt ii) []) = return Done
          step (OIEF svS@(SvS s tt ii) (x:xs)) =
            return $ Yield (SvS s (tt:.TreeIxR frst jl x) (ii:.:RiTirO x)) (OIEF svS xs) 
          step (OIT svS@(SvS s tt ii) (T i)) =
            return $ Yield (SvS s (tt:.TreeIxR frst jl (E i)) (ii:.:RiTirO (T i))) OIFinis
          step (OIFE svS@(SvS s tt ii) (F i)) =
            return $ Yield (SvS s (tt:.TreeIxR frst jl (E $ VG.head i)) (ii:.:RiTirO (F i))) (OIFT svS i $ genTrees frst i) 
          step (OIFT svS@(SvS s tt ii) ss []) = return Done
          step (OIFT svS@(SvS s tt ii) ss (x:xs)) =
            return $ Yield (SvS s (tt:.TreeIxR frst jl (T x)) (ii:.:RiTirO (F $ x `VG.cons` ss))) (OIFT svS ss xs) 
          {-# Inline [0] mk #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}



genTrees frst is = rs
  where 
    i = VG.head is
    p = parent frst VG.! i
    cs = if p >= 0 then children frst VG.! p else roots frst
    rs = VG.toList $ VG.filter (`VG.notElem` is) cs
{-# Inline genTrees #-}


leftSibling d frst k 
  | k >= VG.length (children frst)  = Just d
  | Just l <- lsib frst VG.!? k = Just l
  | otherwise = Nothing
{-# Inline leftSibling #-}





-- * Complemented instances

-- | Outside running index structure requires two local index structures.
-- One is for the inside symbols, one for the outside symbol.

data instance RunningIndex (TreeIxR p v a C) = RiTirC !TFE

-- | Outside works in the opposite direction.
--

instance IndexStream z => IndexStream (z:.TreeIxR p v a C) where
  streamUp   (ls:.TreeIxR p llk lf) (hs:.TreeIxR _ _ ht) = flatten (streamUpMk p lf ht) (streamUpStep   p llk lf ht) $ streamUp ls hs
  streamDown (ls:.TreeIxR p llk lf) (hs:.TreeIxR _ _ ht) = flatten (streamDownMk p lf ht) (streamDownStep p llk lf ht) $ streamDown ls hs
  {-# Inline streamUp #-}
  {-# Inline streamDown #-}

instance RuleContext (TreeIxR p v a C) where
  type Context (TreeIxR p v a C) = ComplementContext
  initialContext _ = Complemented
  {-# Inline initialContext #-}



-- Invisible starting symbol

instance (Monad m) => MkStream m S (TreeIxR p v a C) where
  mkStream S _ (TreeIxR frst lk uu) (TreeIxR _ _ kt)
    = staticCheck (let k = getTFEIx kt;u = getTFEIx uu in k >=0 && k<= u) . singleton . ElmS $ RiTirC kt
  {-# Inline mkStream #-}

instance
  ( Monad m
  , MkStream m S is
  ) => MkStream m S (is:.TreeIxR p v a C) where
  mkStream S (vs:._) (lus:.TreeIxR frst lk uu) (is:.TreeIxR _ _ kt)
    = map (\(ElmS zi) -> ElmS $ zi :.: RiTirC kt)
    . staticCheck (let k = getTFEIx kt;u = getTFEIx uu in k >=0 && k<= u)
    $ mkStream S vs lus is
  {-# INLINE mkStream #-}



instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a I) cs c is (TreeIxR p v a C)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxR p v a I) (cs:.c) (is:.TreeIxR p v a C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:.TreeIxR frst lk v) (is:.TreeIxR _ _ j)
    = map go .addIndexDenseGo cs vs us is
    where go (SvS s tt ii) =
            let RiTirC tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a C))
            in  SvS s (tt:.TreeIxR frst lk tf) (ii:.:RiTirC tf)

instance
  ( IndexHdr s x0 i0 us (TreeIxR p v a O) cs c is (TreeIxR p v a C)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxR p v a O) (cs:.c) (is:.TreeIxR p v a C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:.TreeIxR frst lk v) (is:.TreeIxR _ _ j)
    = map go .addIndexDenseGo cs vs us is
    where go (SvS s tt ii) =
            let RiTirC tf = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a C))
            in  SvS s (tt:.TreeIxR frst lk tf) (ii:.:RiTirC tf)






{-
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

-}

