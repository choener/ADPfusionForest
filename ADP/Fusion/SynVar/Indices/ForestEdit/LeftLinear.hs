
module ADP.Fusion.SynVar.Indices.ForestEdit.LeftLinear where

import           Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import           Prelude hiding (map)
import qualified Data.Vector.Generic as VG

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
  addIndexDenseGo (cs:._) (vs:.OStatic ()) (us:.TreeIxL frst lc l u) (is:.TreeIxL _ _ i j)  -- static = rechts!
    = map go . addIndexDenseGo cs vs us is
    where
      go (SvS s tt ii) =
        let RiTilO iii iij ooi ooj = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL Post v a O))
        in  SvS s (tt:.TreeIxL frst lc 0 j) (ii:.:RiTilO i j 0 j)
  -- TODO do we need to filter out everything that is not "almost
  -- right-most", where only a single tree will then be? This will go into
  -- the territory of linear vs. context-free languages for tree-editing.
  --
  -- \hat{F} -> \hat{F} T
  -- [0,i)   -> [0,j)   [i,j)
  -- @
  --
  addIndexDenseGo (cs:._) (vs:.ORightOf ()) (us:.TreeIxL frst lc l u) (is:.TreeIxL _ _ i j) --variable = links!
    = map go . addIndexDenseGo cs vs us is . staticCheck (rt>=0)
    where
      !rt = rsib frst VG.! (j-1) -- right-tree for this missing forest
      go (SvS s tt ii) =
        let RiTilO iii iij ooi ooj = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL Post v a O))
        in SvS s (tt:.TreeIxL frst lc 0 (rt+1)) (ii:.:RiTilO iii iij 0 (rt+1))
  {-# Inline addIndexDenseGo #-}

instance (MinSize c) => TableStaticVar (u O) c (TreeIxL Post v a O) where 
  tableStaticVar _ _ (OStatic  ()) _ = ORightOf   ()
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
    = map go . addIndexDenseGo cs vs us is . staticCheck (rt>=0)
    where
      !rt = rsib frst VG.! (j-1) -- right-tree for this missing forest
      go (SvS s tt ii) =
        let RiTilO iii iij ooi ooj = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL Post v a O))
        in  SvS s (tt:.TreeIxL frst lc i (rt+1)) (ii:.:RiTilO i (rt+1) ooi ooj)
  -- TODO do we need to filter out everything that is not "almost
  -- right-most", where only a single tree will then be? This will go into
  -- the territory of linear vs. context-free languages for tree-editing.
  --
  -- \hat{T} -> F      \hat{F}
  -- [i,j)   -> [0,i)  [0,j)
  -- @
  --
  addIndexDenseGo (cs:._) (vs:.OFirstLeft ()) (us:.TreeIxL frst lc l u) (is:.TreeIxL _ _ i j) --variable = links!
    = map go . addIndexDenseGo cs vs us is
    where
      go (SvS s tt ii) =
        let RiTilO iii iij ooi ooj = getIndex (getIdx s) (Proxy :: PRI is (TreeIxL Post v a O))
        in SvS s (tt:.TreeIxL frst lc 0 i) (ii:.:RiTilO 0 i ooi ooj)
  {-# Inline addIndexDenseGo #-}

instance (MinSize c) => TableStaticVar (u I) c (TreeIxL Post v a O) where 
  tableStaticVar _ _ (OStatic  ()) _ = ORightOf   ()
  tableStaticVar _ _ (ORightOf ()) _ = OFirstLeft ()
  tableStaticVar _ _ z             _ = z
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

