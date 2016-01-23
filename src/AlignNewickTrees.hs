
module Main where

import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import Control.Monad(forM_)
import Data.Vector.Fusion.Util
import qualified Data.Tree as T
import Debug.Trace

import ADP.Fusion
import Data.PrimitiveArray as PA hiding (map)
import FormalLanguage.CFG
import Data.Forest.Static (TreeOrder(..),Forest)
import qualified Data.Forest.Static as F
import Biobase.Newick

import Data.Forest.Static.ADP


[formalLanguage|
Verbose

Grammar: Global
N: T
N: F
T: n
S: [F,F]
[F,F] -> iter  <<< [T,T] [F,F]
[T,T] -> indel <<< [-,n] [F,F]
[T,T] -> delin <<< [n,-] [F,F]
[T,T] -> align <<< [n,n] [F,F]
[F,F] -> done  <<< [e,e]
--[T,T] -> done  <<< [e,e]   --align (sub)tree with empty (sub)tree
//

Emit: Global
|]

makeAlgebraProduct ''SigGlobal

score :: Monad m => SigGlobal m Int Int Info Info
score = SigGlobal
  { done  = \ (Z:.():.()) -> 0 -- traceShow "EEEEEEEEEEEEE" 0
  , iter  = \ t f -> traceShow ("TFTFTFTFTF",t,f) $ t+f
  , align = \ (Z:.a:.b) f -> traceShow ("ALIGN",f,a,b) $ f + if label a == label b then 100 else -11
  , indel = \ (Z:.():.b) f -> traceShow ("INDEL",f,b) $ f - 5
  , delin = \ (Z:.a:.()) f -> traceShow ("DELIN",f,a) $ f - 3
  , h     = SM.foldl' max (-88888)
  }
{-# Inline score #-}


pretty :: Monad m => SigGlobal m [(Info,Info)] [[(Info,Info)]] Info Info
pretty = SigGlobal
  { done  = \ (Z:.():.()) -> [] -- [(Info "" 0, Info "" 0)]
  , iter  = \ t f -> t++f -- (Info "i1" 0, Info "i2" 0) : t ++ f
  , align = \ (Z:.a:.b) f -> (a,b) : f
  , indel = \ (Z:.():.b) f -> (Info "-" 0,b) : f
  , delin = \ (Z:.a:.()) f -> (a,Info "-" 0) : f
  , h     = SM.toList
  }
{-# Inline pretty #-}



type Trix = TreeIxR Pre V.Vector Info I
type Tbl x = ITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) x
type Frst = Forest Pre V.Vector Info

runForward :: Frst -> Frst -> Z:.Tbl Int:.Tbl Int
runForward f1 f2 = mutateTablesDefault $
                   gGlobal score
                   (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                   (node $ F.label f1)
                   (node $ F.label f2)



run :: Frst -> Frst -> (Z:.Tbl Int:.Tbl Int,Int,[[(Info,Info)]])
run f1 f2 = (fwd,unId $ axiom f,take 1 . unId $ axiom fb)
  where fwd@(Z:.f:.t) = runForward f1 f2
        Z:.fb:.tb = gGlobal (score <|| pretty) (toBacktrack f (undefined :: Id a -> Id a)) (toBacktrack t (undefined :: Id a -> Id a))  
                    (node $ F.label f1) (node $ F.label f2)


--         a            a
--        / \          / \
--       e   d        b   f
--      / \              / \
--     b   c            c   d
--
--                  (a,a)                 100
--              /          \
--         (e,-)            (-,f)         (-3) (-5)
--        /     \          /     \
--   (b,b)       (c,-) (-,c)      (d,d)   100  (-3) (-5) 100
--
--
--
--         (a,a)                          100
--        /     \
--   (-,b)       (-,f)                    (-5) (-5)
--              /     \
--         (e,-)       (d,d)              (-3)  100
--        /     \
--   (b,-)       (c,c)                    (-3)  100

test = do
--  let t1 = f "((b,c)e,d)a;"    -- '-3'
--      t2 = f "(b,(c,d)f)a;"
  let t1 = f "(b:1,c:1)a:1;"
      t2 = f "b:2;c:2;"
      f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
  print t1
  putStrLn ""
  print t2
  putStrLn ""
  let (Z:.ITbl _ _ _ f _:.ITbl _ _ _ t _,sc,bt) = run t1 t2 -- (t2 {F.lsib = VG.fromList [-1,-1], F.rsib = VG.fromList [-1,-1]})
  mapM_ print $ assocs f
  print ""
  mapM_ print $ assocs t
  --print f
  --print t
  forM_ bt $ \b -> do
    putStrLn ""
    forM_ b $ \x -> print x
  print sc


main :: IO ()
main = return ()

