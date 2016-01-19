
module Main where

import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector as V
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
S: F
F -> done  <<< e
F -> iter  <<< T F
T -> done  <<< e
T -> align <<< n F
--T -> indel <<< - F
--T -> delin <<< n F
//

Emit: Global
|]

makeAlgebraProduct ''SigGlobal

score :: Monad m => SigGlobal m Int Int Info
score = SigGlobal
  { done  = \ () -> traceShow "EEEEEEEEEEEEE" 0 
  , iter  = \ t f -> traceShow ("TFTFTFTFTF",t,f) $ t+f
  , align = \ a f -> traceShow ("ALIGN",f,a) $ f + 1
--  , indel = \ (Z:.():.b) f -> traceShow ("INDEL",f) $ f - 1 
--  , delin = \ (Z:.a:.()) f -> traceShow ("DELIN",f) $ f - 1
  , h     = SM.foldl' max (-99999)
  }
{-# Inline score #-}


pretty :: Monad m => SigGlobal m [(Info)] [[(Info)]] Info
pretty = SigGlobal
  { done  = \ () -> [(Info "bla" 0)]
  , iter  = \ t f -> t ++ f
  , align = \ a f -> (a) : f
--  , indel = \ (b) f -> (b) : f
--  , delin = \ (Z:.a:.()) f -> (a,Info "" 0) : f
  , h     = SM.toList
  }
{-# Inline pretty #-}


type Trix = TreeIxR Pre V.Vector Info I
type Tbl x = ITbl Id Unboxed EmptyOk Trix x
type Frst = Forest Pre V.Vector Info

runForward :: Frst -> Frst -> Z:.Tbl Int:.Tbl Int
runForward f1 f2 = mutateTablesDefault $
                   gGlobal score
                   (ITbl 0 1 EmptyOk (PA.fromAssocs (minIx f1) (maxIx f1) (-99999) [] ))
                   (ITbl 0 0 EmptyOk (PA.fromAssocs (minIx f1) (maxIx f1) (-99999) [] ))
                   (node $ F.label f1)




run :: Frst -> Frst -> (Z:.Tbl Int:.Tbl Int,[[(Info)]])
run f1 f2 = (fwd,take 1 . unId $ axiom fb)
  where fwd@(Z:.f:.t) = runForward f1 f2
        Z:.fb:.tb = gGlobal (score <|| pretty) (toBacktrack f (undefined :: Id a -> Id a)) (toBacktrack t (undefined :: Id a -> Id a))  
                    (node $ F.label f1)


test = do
  let t1 = f "x;" --"((b,c)e,d)a;"
      --t2 = f "(b,(c,d)f)a;"
      f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
  print t1
  putStrLn ""
  --print t2
  putStrLn ""
  let (Z:.ITbl _ _ _ f _:.ITbl _ _ _ t _,bt) = run t1 t1
  print f
  print t
  print bt

main :: IO ()
main = return ()

