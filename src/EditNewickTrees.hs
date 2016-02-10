
module Main where

import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import Control.Monad(forM_)
import Data.Vector.Fusion.Util
import qualified Data.Tree as T
import Debug.Trace
import Data.List (nub)

import ADP.Fusion
import Data.PrimitiveArray as PA hiding (map)
import FormalLanguage.CFG
import Data.Forest.Static (TreeOrder(..),Forest)
import qualified Data.Forest.Static as F
import Biobase.Newick

import Data.Forest.Static.Left
import Data.Forest.Static.Node

[formalLanguage|
Verbose

Grammar: Global
N: T
N: F
T: n
T: x
S: [F,F]
[F,F] -> iter   <<< [F,F] [T,T]
[F,F] -> indel  <<< [F,F] [-,x]
--[F,F] -> findel <<< [-,x] [F,F]
[F,F] -> delin  <<< [F,F] [x,-]
--[F,F] -> delfin <<< [x,-] [F,F]
[T,T] -> align  <<< [n,n] [F,F]
[F,F] -> done   <<< [e,e]
-- how to delete roots? does this grammar work? 
-- example trees: 
--  d   c
--  |   |
--  c   d
--
//

Emit: Global
|]


makeAlgebraProduct ''SigGlobal



score :: Monad m => SigGlobal m Int Int Info Info Info Info
score = SigGlobal
  { align = \( Z:.n0:.n1) f -> f + if label n0 == label n1 then 100 else -1111
  , done = \(Z:.():.()) -> 0
  , iter = \ f t -> f+t
  , indel = \ f (Z:.():.n1) -> f - 3
  , delin = \ f (Z:.n0:.()) -> f - 5
  , h = SM.foldl' max (-77777) 
}
{-# Inline score #-}

{-
  { done  = \ (Z:.():.()) -> 0 -- traceShow "EEEEEEEEEEEEE" 0
  , iter  = \ f t -> tSI glb ("TFTFTFTFTF",f,t) $ t+f
  , align = \ (Z:.a:.b) f -> tSI glb ("ALIGN",f,a,b) $ f + if label a == label b then 100 else -11
  , indel = \ (Z:.():.b) f -> tSI glb ("INDEL",f,b) $ f - 5
  , delin = \ (Z:.a:.()) f -> tSI glb ("DELIN",f,a) $ f - 3
  , h     = SM.foldl' max (-88888)
  }


type Pretty = [[(Info,Info)]]
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
-}

type Pretty' = [[T.Tree (Info,Info)]]
pretty' :: Monad m => SigGlobal m [T.Tree (Info,Info)] [[T.Tree ((Info,Info))]] Info Info Info Info
pretty' = SigGlobal
  { done  = \ (Z:.():.()) -> []
  , iter  = \ f t -> f++t
  , align = \ (Z:.a:.b) f -> [T.Node (a,b) f]
  , indel = \ f (Z:.():.b) -> f --[T.Node (Info "-" 0,b) f]
  , delin = \ f (Z:.a:.()) -> f --[T.Node (a,Info "-" 0) f]
  , h     = SM.toList
  }
{-# Inline pretty' #-}



type Trix = TreeIxL Pre V.Vector Info I
type Tbl x = ITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) x
type Frst = Forest Pre V.Vector Info

runForward :: Frst -> Frst -> Z:.Tbl Int:.Tbl Int
runForward f1 f2 = mutateTablesDefault $
                   gGlobal score
                   (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                   (node $ F.label f1)
                   (node $ F.label f2)
                   (node $ F.label f1)
                   (node $ F.label f2)



run :: Frst -> Frst -> (Z:.Tbl Int:.Tbl Int,Int,Pretty')
run f1 f2 = (fwd,unId $ axiom f, unId $ axiom fb)
  where fwd@(Z:.f:.t) = runForward f1 f2
        Z:.fb:.tb = gGlobal (score <|| pretty') (toBacktrack f (undefined :: Id a -> Id a)) (toBacktrack t (undefined :: Id a -> Id a))  
                    (node $ F.label f1) (node $ F.label f2)
                    (node $ F.label f1) (node $ F.label f2)



test = do
  let t2 = f "c;" --"(a,(b)c)d;"--"((b,c)e,d)a;"
      t1 = f "c;" --"((a,b)d)c;"--"(b,(c,d)f)a;"
--  let t1 = f "d;(b)e;" -- (b,c)e;"    -- '-3'
--      t2 = f "(d)f;b;" -- b;"
--  let t1 = f "(b:1,c:1)a:1;"
--      t2 = f "b:2;c:2;"
      f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x  -- editing needs postorder
  print t1
  putStrLn ""
  print t2
  putStrLn ""
  let (Z:.ITbl _ _ _ f _:.ITbl _ _ _ t _,sc,bt') = run t1 t2 -- (t2 {F.lsib = VG.fromList [-1,-1], F.rsib = VG.fromList [-1,-1]})
  mapM_ print $ assocs f
  print ""
  mapM_ print $ assocs t
  --print f
  --print t
  let bt = take 10 $ nub bt'
  print (length bt', length bt)
  forM_ bt $ \b -> do
    putStrLn ""
    forM_ b $ \x -> putStrLn $ T.drawTree $ fmap show x
  print sc


main :: IO ()
main = return ()



