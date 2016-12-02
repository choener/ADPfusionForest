
module ADP.Fusion.SynVar.Indices.ForestEdit.LeftLinear where

import           Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import           Prelude hiding (map)
import qualified Data.Vector.Generic as VG
import           Debug.Trace
import           Data.List (sort,nub)

import           ADP.Fusion.Core
import           Data.Forest.Static
import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Core.ForestEdit.LeftLinear



-- * Inside indices, Inside object

instance
  ( IndexHdr s x0 i0 us (TreeIxL p v a I) cs c is (TreeIxL p v a I)
  , MinSize c
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
  {-# Inline addIndexDenseGo #-}

instance (MinSize c) => TableStaticVar u c (TreeIxL p v a I) where 
  tableStaticVar _ _ _ _ = IVariable ()
  tableStreamIndex _ c _ = id
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}



-- * Grammar: Outside; Table: Outside

instance
  ( IndexHdr s x0 i0 us (TreeIxL Post v a O) cs c is (TreeIxL Post v a O)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxL Post v a O) (cs:.c) (is:.TreeIxL Post v a O) where
  --
  -- \hat{T} -> F      \hat{F}
  -- [i,j)   -> [0,i)  [0,j)
  -- @
  --
  -- TODO in case this is a @Tree@, not a @Forest@, then we should only
  -- return some value, if @i,j@ is proper.
  --
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (us:.TreeIxL frst lc l u) (is:.TreeIxL _ _ i j)  -- static = rechts!
    = map go . addIndexDenseGo cs vs us is
    where
      go (SvS s tt ii) =
        let RiTilO iii iij ooi ooj = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL Post v a O))
        in  traceShow (ss "O/O/st",(i,j),(ooi,j)) $
            SvS s (tt:.TreeIxL frst lc ooi j) (ii:.:RiTilO iii iij ooi j)
  -- TODO do we need to filter out everything that is not "almost
  -- right-most", where only a single tree will then be? This will go into
  -- the territory of linear vs. context-free languages for tree-editing.
  --
  -- \hat{F} -> \hat{F} T
  -- [0,i)   -> [0,j)   [i,j)
  -- @
  --
  -- TODO use ooi, ooj instead of i,j for CFG-style grammars
  addIndexDenseGo (cs:._) (vs:.ORightOf ()) (us:.TreeIxL frst lc l u) (is:.TreeIxL _ _ i j) --variable = links!
    = blub . flatten mk step . addIndexDenseGo cs vs us is
    where mk svs = return (svs, Prelude.filter (\z -> j == lc VG.! z) $ toRoot frst j)
          -- ^ the @filter@ makes sure that we only build trees whose
          -- left-most leaf is @j@. Since then forest and tree fit next to
          -- each other.
          step (_,[]) = return Done
          -- a tree we can place to the right of us: @[j,k+1)@
          -- we ourselves make a whole @[i,k+1)@ in which to place said
          -- tree.
          step (SvS s tt ii,k:ks) = do
            let RiTilO iii iij ooi ooj = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL Post v a O))
            traceShow (ss "OOvar",i,j,(i,k+1),(j,k+1)) . return $ Yield (SvS s (tt:.TreeIxL frst lc i (k+1)) (ii:.:RiTilO j (k+1) i (k+1))) (SvS s tt ii, ks)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
          blub = if False -- (i,j) == (0,1)
                 then traceShow (ss "blub",i,j, let rs = toRoot frst j in (rs, [r | r <- rs, j == lc VG.! r]))
                 else id
  {-# Inline addIndexDenseGo #-}

toRoot frst k = goR k
  where goR (-1) = []
        goR k | k >= VG.length (parent frst) = []
        goR k    = k : goR (parent frst VG.! k)

ss :: String -> String
ss = id

instance (MinSize c) => TableStaticVar (u O) c (TreeIxL Post v a O) where 
  tableStaticVar _ _ (OStatic  ()) _ = OFirstLeft ()
  tableStaticVar _ _ (ORightOf ()) _ = OFirstLeft ()
  tableStaticVar _ _ z             _ = z
  tableStreamIndex _ c _ = id
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}



-- * Grammar: Outside; Table: Inside

instance
  ( IndexHdr s x0 i0 us (TreeIxL Post v a I) cs c is (TreeIxL Post v a O)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxL Post v a I) (cs:.c) (is:.TreeIxL Post v a O) where
  --
  -- \hat{F} -> \hat{F} T
  -- [0,i)   -> [0,j)   [i,j)
  -- @
  --
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (us:.TreeIxL frst lc l u) (is:.TreeIxL _ _ i j)  -- static = rechts!
    = map go . addIndexDenseGo cs vs us is -- . staticCheck (j>0 && rt>=0)
    where
      go (SvS s tt ii) =
        let RiTilO iii iij ooi ooj = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL Post v a O))
        in  if (iij>0 && j == iii && iii == lc VG.! (iij-1))
            then SvS s (tt:.TreeIxL frst lc iii iij) (ii:.:RiTilO iii iij ooi ooj)
            else error $ show (i,j,iii,iij, lc VG.! (iij-1), toRoot frst (j-1))
  -- TODO do we need to filter out everything that is not "almost
  -- right-most", where only a single tree will then be? This will go into
  -- the territory of linear vs. context-free languages for tree-editing.
  --
  -- \hat{T} -> F      \hat{F}
  -- [i,j)   -> [0,i)  [0,j)
  -- @
  --
  addIndexDenseGo (cs:._) (vs:.OFirstLeft ()) (us:.TreeIxL frst lc l u) (is:.TreeIxL _ _ i j) --variable = links!
    = flatten mk step . addIndexDenseGo cs vs us is . staticCheck isValidTree
    where mk svs = return (svs, allLeftBoundForests frst lc (j-1))
          step (s,[]) = return Done
          step (SvS s tt ii,k:ks) = do
            let RiTilO iii iij ooi ooj = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL Post v a O))
            return $ Yield (SvS s (tt:.TreeIxL frst lc k i) (ii:.:RiTilO iii i k j)) (SvS s tt ii,ks) -- j or ooj ???
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
          !isValidTree = j>0 && j<=u -- && (i == lc VG.! (j-1))
  addIndexDenseGo _ (vs:.bang) _ _ = error $ show bang
  {-# Inline addIndexDenseGo #-}

lboundary frst lc k = go k $ lsib frst VG.! k
  where go now next | next == -1 = lc VG.! now
                    | otherwise  = go next (lsib frst VG.! now)

allLeftBoundForests frst lc k = ls
  where rs = goR k
        ls = nub $ sort [ lc VG.! z | z <- rs ]
        goR (-1) = []
        goR k    = k : goR (parent frst VG.! k)

instance (MinSize c) => TableStaticVar (u I) c (TreeIxL Post v a O) where 
  tableStaticVar _ _ (OStatic  ())   _ = ORightOf   ()
  tableStaticVar _ _ (ORightOf ())   _ = OFirstLeft ()
  tableStaticVar _ _ (OFirstLeft ()) _ = OLeftOf    ()
  tableStreamIndex _ c _ = id
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}



-- * Complement

instance
  ( IndexHdr s x0 i0 us (TreeIxL Post v a I) cs c is (TreeIxL Post v a C)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxL Post v a I) (cs:.c) (is:.TreeIxL Post v a C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:.TreeIxL frst lc l u) (is:.TreeIxL _ _ i j)  -- static = rechts!
    = map go . addIndexDenseGo cs vs us is
    where
      go (SvS s tt ii) = SvS s (tt:.TreeIxL frst lc i j) (ii:.:RiTilC i j)
  {-# Inline addIndexDenseGo #-}

instance
  ( IndexHdr s x0 i0 us (TreeIxL Post v a O) cs c is (TreeIxL Post v a C)
  , MinSize c
  ) => AddIndexDense s (us:.TreeIxL Post v a O) (cs:.c) (is:.TreeIxL Post v a C) where
  addIndexDenseGo (cs:._) (vs:.Complemented) (us:.TreeIxL frst lc l u) (is:.TreeIxL _ _ i j)  -- static = rechts!
    = map go . addIndexDenseGo cs vs us is
    where
      go (SvS s tt ii) = SvS s (tt:.TreeIxL frst lc i j) (ii:.:RiTilC i j)
  {-# Inline addIndexDenseGo #-}



instance (MinSize c) => TableStaticVar (u I) c (TreeIxL Post v a C) where 
  tableStaticVar _ _ z             _ = z
  tableStreamIndex _ c _ = id
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}

instance (MinSize c) => TableStaticVar (u O) c (TreeIxL Post v a C) where 
  tableStaticVar _ _ z             _ = z
  tableStreamIndex _ c _ = id
  {-# Inline [0] tableStaticVar #-}
  {-# Inline [0] tableStreamIndex #-}

