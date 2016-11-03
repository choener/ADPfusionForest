
-- | Epsilon
--
-- X    -> ε
-- i,E     i,E    ∀ i

module ADP.Fusion.Term.Epsilon.ForestAlign.RightLinear where

import           Data.Strict.Tuple hiding (fst, snd)
import           Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import           Prelude hiding (map)

import           ADP.Fusion.Core
import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Core.ForestAlign.RightLinear



-- * Inside



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



-- * Outside



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

