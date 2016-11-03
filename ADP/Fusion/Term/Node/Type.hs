
module ADP.Fusion.Term.Node.Type where

import           Data.Strict.Tuple
import qualified Data.Vector.Generic as VG

import           ADP.Fusion.Core
import           Data.PrimitiveArray



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



-- | TODO Should return permutation being used as well This means we have
-- a vector @v@ and a permutation @p@ on @[1 .. |v|]@. We should apply @p@
-- to @v@ yielding @v'@, the permutation of @v@. @PermNode@ should then
-- hold on to the pair @(v',p)@. This allows us to observe the permutation
-- directly via @v'@, but also consider the applied @p@. This is useful for
-- considering what the "cost" of @p@ should be. Say, given @[1,2,3,4]@
-- then the identity permutation is cost-free, while @[2,1,3,4]@ could be
-- less costly than @[4,1,3,2]@, but more costly than @[4,3,2,1]@. This
-- will depend on the user but should be supported.

data PermNode r x where
  PermNode :: VG.Vector v x
       => (v x -> Int -> r)
       -> !(v x)
       -> PermNode r x

permNode :: VG.Vector v x => v x -> PermNode x x
permNode = PermNode (VG.!)
{-# Inline permNode #-}

instance Build (PermNode r x)

instance
  ( Element ls i
  ) => Element (ls :!: PermNode r x) i where
    data Elm (ls :!: PermNode r x) i = ElmPermNode !r !(RunningIndex i) !(Elm ls i)
    type Arg (ls :!: PermNode r x)   = Arg ls :. r
    getArg (ElmPermNode x _ ls) = getArg ls :. x
    getIdx (ElmPermNode _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}


type instance TermArg (PermNode r x) = r

