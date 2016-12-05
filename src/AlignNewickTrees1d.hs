
module Main where

import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Data.Tree as T
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as SM

import           ADP.Fusion.Core
import           Biobase.Newick
import           Data.Forest.Static (TreeOrder(..),Forest)
import           Data.PrimitiveArray as PA hiding (map)
import           FormalLanguage.CFG
import qualified Data.Forest.Static as F
import           Data.Forest.Static.Node

import           ADP.Fusion.Forest



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
  , align = \ a f -> traceShow ("ALIGN",f,a) $ f + 100
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
type Tbl x = TwITbl Id Unboxed EmptyOk Trix x
type Frst = Forest Pre V.Vector Info
type TblBt x = TwITblBt Unboxed EmptyOk Trix Int Id Id [x]
type B = Info

runForward :: Frst -> Frst -> Z:.Tbl Int:.Tbl Int
runForward f1 f2 = mutateTablesDefault $
                   gGlobal score
                   (ITbl 0 1 EmptyOk (PA.fromAssocs (minIx f1) (maxIx f1) (-99999) [] ))
                   (ITbl 0 0 EmptyOk (PA.fromAssocs (minIx f1) (maxIx f1) (-99999) [] ))
                   (node NTany $ F.label f1)




run :: Frst -> Frst -> (Z:.Tbl Int:.Tbl Int,Int,[[(Info)]])
run f1 f2 = (fwd,unId $ axiom f,take 1 . unId $ axiom fb)
  where fwd@(Z:.f:.t) = runForward f1 f2
        Z:.fb:.tb = gGlobal (score <|| pretty) (toBacktrack f (undefined :: Id a -> Id a)) (toBacktrack t (undefined :: Id a -> Id a))  
                    (node NTany $ F.label f1)
                    :: Z:.TblBt B:.TblBt B


test = do
  let t1 = f "(d,b,c)a;" --"((b,c)e,d)a;"
      --t2 = f "(b,(c,d)f)a;"
      f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
  print t1
  putStrLn ""
  --print t2
  putStrLn ""
  let (Z:.TW (ITbl _ _ _ f) _:.TW (ITbl _ _ _ t) _,sc,bt) = run t1 t1
  print f
  print t
  print bt
  print sc

main :: IO ()
main = return ()

