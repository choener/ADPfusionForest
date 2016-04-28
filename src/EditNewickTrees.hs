
module Main where

import           Control.Monad(forM_,unless)
import           Data.List (nub,tails)
import           Data.Text (Text)
import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Data.Tree as T
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Generic as VG
import           System.Console.CmdArgs
import           System.Exit (exitFailure)
import           Text.Printf
import qualified Data.Text as Text

import           ADP.Fusion
import           Biobase.Newick
import           Data.Forest.Static (TreeOrder(..),Forest)
import           Data.PrimitiveArray as PA hiding (map)
import           FormalLanguage.CFG
import qualified Data.Forest.Static as F

import           Data.Forest.Static.EditLL
import           Data.Forest.Static.Node

[formalLanguage|
Verbose

Grammar: Global
N: T
N: F
T: x
S: [F,F]
[F,F] -> iter   <<< [F,F] [T,T]
[F,F] -> indel  <<< [F,F] [-,x]
[F,F] -> delin  <<< [F,F] [x,-]
[T,T] -> align  <<< [F,F] [x,x]
[F,F] -> done   <<< [e,e]
//

Emit: Global
|]


makeAlgebraProduct ''SigGlobal



score :: Monad m => Int -> Int -> Int -> SigGlobal m Int Int Info Info
score mat mis ndl = SigGlobal
  { align = \ f ( Z:.n0:.n1) -> f + if label n0 == label n1 then mat else mis
  , done = \(Z:.():.()) -> 0
  , iter = \ f t -> f+t
  , indel = \ f (Z:.():.n1) -> f + ndl
  , delin = \ f (Z:.n0:.()) -> f + ndl
  , h = SM.foldl' max (-77777) 
}
{-# Inline score #-}


type Pretty' = [[(Info,Info)]]
pretty' :: Monad m => SigGlobal m [(Info,Info)] [[(Info,Info)]] Info Info
pretty' = SigGlobal
  { done  = \ (Z:.():.()) -> []
  , iter  = \ f t -> f++t
  , align = \ f (Z:.a:.b) -> (a,b) : f
  , indel = \ f (Z:.():.b) -> (Info "-" 0,b) : f
  , delin = \ f (Z:.a:.()) -> (a,Info "-" 0) : f
  , h     = SM.toList
  }
{-# Inline pretty' #-}



type Trix = TreeIxL Post V.Vector Info I
type Tbl x = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) x
type TblBt x = TwITblBt Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) Int Id Id [x]
type Frst = Forest Post V.Vector Info
type B = (Info,Info)

runForward :: Int -> Int -> Int -> Frst -> Frst -> Z:.Tbl Int:.Tbl Int
runForward mat mis ndl f1 f2
  = mutateTablesDefault $
      gGlobal (score mat mis ndl)
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
      (node $ F.label f1)
      (node $ F.label f2)
{-# NoInline runForward #-}


run :: Int -> Int -> Int -> Frst -> Frst -> (Z:.Tbl Int:.Tbl Int,Int,Pretty')
run mat mis ndl f1 f2 = (fwd,unId $ axiom f, unId $ axiom fb)
  where fwd@(Z:.f:.t) = runForward mat mis ndl f1 f2
        Z:.fb:.tb = gGlobal (score mat mis ndl <|| pretty') (toBacktrack f (undefined :: Id a -> Id a)) (toBacktrack t (undefined :: Id a -> Id a))  
                    (node $ F.label f1) (node $ F.label f2)
                    :: Z:.TblBt B:.TblBt B
{-# NoInline run #-}



testedit = do
  -- c        c
  -- |       / \
  -- b      a   b
  -- |
  -- a
  let t2 = f "((a)b)c;" --"(a,(b)c)d;"--"((b,c)e,d)a;"
      t1 = f "(a,b)c;" --"((a,b)d)c;"--"(b,(c,d)f)a;"
--  let t1 = f "d;(b)e;" -- (b,c)e;"    -- '-3'
--      t2 = f "(d)f;b;" -- b;"
--  let t1 = f "(b:1,c:1)a:1;"
--      t2 = f "b:2;c:2;"
--  let t1 = f "((d,e,f)b,(z)c)a;" --"((a,b)y,c)z;" --"((d,e,i)b,c)a;" --"((a,(b)c)d,e)f;"
--      t2 = f "(((d,e)y,f)b,((x)c,i)g)a;" --"(a,b,c)z;" --"((d,e)b,(f)h,(c,i)g)a;" --"(((a,b)d)c,e)f;"
--  let t1 = f "((a,(b)c)d,e)f;"
--      t2 = f "(((a,b)d)c,e)f;"
      f :: Text -> F.Forest Post V.Vector Info
      f x = either error (F.forestPost . map getNewickTree) $ newicksFromText x  -- editing needs postorder
  print t1
  print $ F.leftMostLeaves t1
  print $ F.leftKeyRoots t1
  putStrLn ""
  print t2
  print $ F.leftMostLeaves t2
  print $ F.leftKeyRoots t2
  putStrLn ""
  let (Z:.TW (ITbl _ _ _ f) _:.TW (ITbl _ _ _ t) _,sc,bt') = run 1 (-3) (-1) t1 t2 -- (t2 {F.lsib = VG.fromList [-1,-1], F.rsib = VG.fromList [-1,-1]})
  mapM_ print $ assocs f
  print ""
  mapM_ print $ assocs t
  --print f
  --print t
  print $ F.leftKeyRoots t1
  print $ F.leftKeyRoots t2
  let bt = take 10 $ nub bt'
  print (length bt', length bt)
  forM_ bt $ \b -> do
    putStrLn ""
    forM_ b $ \x -> print x -- putStrLn $ T.drawTree $ fmap show x
  print sc



data Options = Options
  { inputFiles  :: [String]
  , matchSc     :: Int
  , notmatchSc  :: Int
  , delinSc     :: Int
  }
  deriving (Show,Data,Typeable)

oOptions = Options
  { inputFiles  = def &= args
  , matchSc     = 10  &= help "score for match cases, positive number; def=10"
  , notmatchSc  = -30 &= help "score for mismatches, negative number; def=-30"
  , delinSc     = -10 &= help "score for deletions and insertions, negative number; def=-10"
  }

main :: IO ()
main = do
  o@Options{..} <- cmdArgs oOptions
  unless (length inputFiles >= 2) $ do
    putStrLn "give at least two Newick files on the command line"
    exitFailure
  let ts = init $ init $ tails inputFiles
  forM_ ts $ \(n1:hs) -> do
    forM_ hs $ \n2 -> do
      let f x = either error (F.forestPost . map getNewickTree) $ newicksFromText $ Text.pack x
      putStrLn n1
      putStrLn n2
      f1 <- f <$> readFile n1
      f2 <- f <$> readFile n2
      let (_,sc,bt') = run matchSc notmatchSc delinSc f1 f2
      let bt = nub $ take 10 bt'
      printf "Score: %10d\n" sc
      putStrLn ""
      forM_ bt $ \b -> do
        forM_ b $ \(Info l _, Info r _) -> printf "%1s.%1s  " (Text.unpack l) (Text.unpack r)
        putStrLn ""

