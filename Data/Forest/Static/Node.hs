
module Data.Forest.Static.Node where

import           Data.Strict.Tuple
import qualified Data.Vector.Generic as VG

import           ADP.Fusion
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

