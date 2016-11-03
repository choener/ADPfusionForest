
module ADP.Fusion.Term.Deletion.ForestAlign.RightLinear where

import Data.Strict.Tuple hiding (fst, snd)
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Prelude hiding (map)

import ADP.Fusion.Core
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.ForestAlign.RightLinear



-- * Inside



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



-- * Outside
--
-- Has no conditions on when it is acceptable.
--
-- TODO missing single tape instance?



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

