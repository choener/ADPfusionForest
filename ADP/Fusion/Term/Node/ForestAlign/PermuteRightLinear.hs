
-- |
--
-- TODO outside costs

module ADP.Fusion.Term.Node.ForestAlign.PermuteRightLinear where

import           Data.List (permutations)
import           Data.Strict.Tuple hiding (fst, snd)
import           Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import           Prelude hiding (map)
import qualified Data.Vector.Generic as VG
import qualified Data.Vector.Unboxed as VU
import qualified Prelude as P

import           ADP.Fusion.Core
import           Data.Forest.Static
import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Core.ForestAlign.PermuteRightLinear
import           ADP.Fusion.Term.Node.Type



-- Node: parse a local root

instance
  ( TmkCtx1 m ls (Node r x) (TreeIxR p v a t)
  ) => MkStream m (ls :!: Node r x) (TreeIxR p v a t) where
  mkStream (ls :!: Node f nty xs) sv us is
    = map (\(ss,ee,ii) -> ElmNode ee ii ss)
    . addTermStream1 (Node f nty xs) sv us is
    $ mkStream ls (termStaticVar (Node f nty xs) sv is) us (termStreamIndex (Node f nty xs) sv is)
  {-# Inline mkStream #-}



-- |
--
-- X    -> n    Y
-- i,T  -> i,T  (i+1),t    -- @t@ = if @i@ has no children, then @E@, else @F@.

instance
  ( TstCtx m ts s x0 i0 is (TreeIxR p v a I)
--  , Show r
  ) => TermStream m (TermSymbol ts (Node r x)) s (is:.TreeIxR p v a I) where
  termStream (ts:|Node f nty xs) (cs:.IVariable ()) (us:.TreeIxR _ ul utfe) (is:.TreeIxR frst il itfe)
    = map (\(TState s ii ee) ->
              let RiTirI (T l) = getIndex (getIdx s) (Proxy :: PRI is (TreeIxR p v a I))
                  cs = children frst VG.! l
                  fe = if VG.null cs then E l else F cs
              in  -- traceShow ("N"::String,cs,fe, f xs l) $
                  TState s (ii:.:RiTirI fe) (ee:.f xs l) )
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

