
module ADP.Fusion.Term.Node.ForestAlign.RightLinear where

import           Data.Strict.Tuple hiding (fst, snd)
import           Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import           Prelude hiding (map)
import qualified Data.Vector.Generic as VG

import           ADP.Fusion.Core
import           Data.Forest.Static
import           Data.PrimitiveArray hiding (map)

import           ADP.Fusion.Core.ForestAlign.RightLinear
import           ADP.Fusion.Term.Node.Type



-- * Inside

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



-- * Outside

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



