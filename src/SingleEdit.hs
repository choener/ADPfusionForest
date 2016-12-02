
module Main where

import           Data.Char (toLower)
import           System.FilePath
import           Control.Monad(forM_,unless)
import           Data.List (nub,tails)
import           Data.Text (Text)
import           Data.Vector.Fusion.Util
import           Debug.Trace
import           Numeric.Log
import qualified Data.Text as Text
import qualified Data.Tree as T
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Generic as VG
import           System.Console.CmdArgs
import           System.Exit (exitFailure)
import           Text.Printf
import           Unsafe.Coerce

import           ADP.Fusion.Core
import           Biobase.Newick
import           Data.Forest.Static (TreeOrder(..),Forest)
import           Data.PrimitiveArray as PA hiding (map)
import           FormalLanguage.CFG
import qualified Data.Forest.Static as F
import           Diagrams.TwoD.ProbabilityGrid

import           ADP.Fusion.Forest.Edit.LL



[formalLanguage|
Verbose

Grammar: Global
N: T
N: F
T: x
S: F
F -> iter   <<< F T
T -> align  <<< F x
F -> done   <<< e
//
Outside: Labolg
Source: Global
//

Emit: Global
Emit: Labolg
|]


makeAlgebraProduct ''SigGlobal



score :: Monad m => Int -> Int -> Int -> SigGlobal m Int Int Info
score mat mis ndl = SigGlobal
  { gAlign = \ f n -> f + mat
  , gDone = \() -> 0
  , gIter = \ f t -> f+t
  , gH = SM.foldl' max (-77777)
}
{-# Inline score #-}

resig :: Monad m => SigGlobal m a b c -> SigLabolg m a b c
resig (SigGlobal gal gdo git gh) = SigLabolg gal gdo git gh
{-# Inline resig #-}


type Pretty' = [Info]
pretty' :: Monad m => SigGlobal m [Info] [[Info]] Info
pretty' = SigGlobal
  { gDone  = \ () -> []
  , gIter  = \ f t -> f++t
  , gAlign = \ f a -> a : f
  , gH     = SM.toList
  }
{-# Inline pretty' #-}

part :: Monad m => Log Double -> Log Double -> Log Double -> SigGlobal m (Log Double) (Log Double) Info
part mat mis ndl = SigGlobal
  { gAlign = \ f n -> f * mat
  , gDone = \() -> 1
  , gIter = \ f t -> f * t
  , gH = SM.foldl' (+) 0.00000
}
{-# Inline part #-}



type Trix = TreeIxL Post V.Vector Info I
type Tbl x = TwITbl Id Unboxed EmptyOk Trix x
type TblBt x = TwITblBt Unboxed EmptyOk Trix Int Id Id [x]
type Frst = Forest Post V.Vector Info
type B = Info
type Trox = TreeIxL Post V.Vector Info O
type OTbl x = TwITbl Id Unboxed EmptyOk Trox x

runForward :: Int -> Int -> Int -> Frst -> Z:.Tbl Int:.Tbl Int
runForward mat mis ndl f1
  = mutateTablesDefault $
      gGlobal (score mat mis ndl)
      (ITbl 0 1 EmptyOk (PA.fromAssocs (minIx f1) (maxIx f1) (-99999) [] ))
      (ITbl 0 0 EmptyOk (PA.fromAssocs (minIx f1) (maxIx f1) (-99999) [] ))
      (node $ F.label f1)
{-# NoInline runForward #-}

runInside :: (Log Double) -> (Log Double) -> (Log Double) -> Frst -> Z:.Tbl (Log Double):.Tbl (Log Double)
runInside mat mis ndl f1
  = mutateTablesDefault $
      gGlobal (part mat mis ndl)
      (ITbl 0 1 EmptyOk (PA.fromAssocs (minIx f1) (maxIx f1) 0 [] ))
      (ITbl 0 0 EmptyOk (PA.fromAssocs (minIx f1) (maxIx f1) 0 [] ))
      (node $ F.label f1)
{-# NoInline runInside #-}

runOutside :: (Log Double) -> (Log Double) -> (Log Double) -> Frst -> Z:.Tbl (Log Double):.Tbl (Log Double) -> Z:.OTbl (Log Double):.OTbl (Log Double)
runOutside mat mis ndl f1 (Z:.iF:.iT)
  = mutateTablesDefault $
      gLabolg (resig (part mat mis ndl))
      (ITbl 0 0 EmptyOk (PA.fromAssocs (minIx f1) (maxIx f1) 0 [] ))
      (ITbl 0 1 EmptyOk (PA.fromAssocs (minIx f1) (maxIx f1) 0 [] ))
      iF
      iT
      (node $ F.label f1)
{-# NoInline runOutside #-}


run :: Int -> Int -> Int -> Frst -> (Z:.Tbl Int:.Tbl Int,Int,[[B]])
run mat mis ndl f1 = (fwd,unId $ axiom f, unId $ axiom fb)
  where fwd@(Z:.f:.t) = runForward mat mis ndl f1
        Z:.fb:.tb = gGlobal
                      (score mat mis ndl <|| pretty')
                      (toBacktrack f (undefined :: Id a -> Id a))
                      (toBacktrack t (undefined :: Id a -> Id a))
                      (node $ F.label f1)
                    :: Z:.TblBt B:.TblBt B
{-# NoInline run #-}

runIO f1 matchSc mismatchSc indelSc temperature = (fwd,out,unId $ axiom f)
  where fwd@(Z:.f:.t) = runInside matchSc mismatchSc indelSc f1
        out@(Z:.oft:.ott) = runOutside matchSc mismatchSc indelSc f1 fwd
{-# NoInline runIO #-}


{-
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
-}

data PFT = SVG | EPS
  deriving (Show,Data,Typeable)


data Options = Options
  { inputFiles  :: String
  , probFile    :: String
  , probFileTy  :: PFT
  , linearScale :: Bool
  , matchSc     :: Double
  , notmatchSc  :: Double
  , delinSc     :: Double
  , temperature :: Double
  }
  deriving (Show,Data,Typeable)

oOptions = Options
  { inputFiles  = def &= args
  , matchSc     = 10  &= help "score for match cases, positive number; def=10"
  , notmatchSc  = -30 &= help "score for mismatches, negative number; def=-30"
  , delinSc     = -10 &= help "score for deletions and insertions, negative number; def=-10"
  , probFile = def
  , probFileTy = EPS
  , linearScale = False
  , temperature = 1
  }

main :: IO ()
main = do
  o@Options{..} <- cmdArgs oOptions
  return ()
  {-
  unless (length inputFiles >= 2) $ do
    putStrLn "give at least two Newick files on the command line"
    exitFailure
  let ts = init $ init $ tails inputFiles
      expScore z = Exp $ z/temperature 
  forM_ ts $ \(n1:hs) -> do
    forM_ hs $ \n2 -> do
      let fff x = either error (F.forestPost . map getNewickTree) $ newicksFromText $ Text.pack x
      putStrLn n1
      putStrLn n2
      f1 <- readFile n1
      f2 <- readFile n2
      let (_,sc,bt') = run (round matchSc) (round notmatchSc) (round delinSc) (fff f1) (fff f2)
      let bt = nub $ take 10 bt'
      printf "Score: %10d\n" sc
      putStrLn ""
      forM_ bt $ \b -> do
        forM_ b $ \(Info l _, Info r _) -> printf "%1s.%1s  " (Text.unpack l) (Text.unpack r)
        putStrLn ""
      unless (null probFile) $ do
        runAlignIO (if linearScale then FWlinear else FWlog) probFileTy (probFile ++ "-" ++ takeBaseName n1 ++ "-" ++ takeBaseName n2 ++ "." ++ (map toLower $ show probFileTy)) f1 f2 (expScore matchSc) (expScore notmatchSc) (expScore delinSc) (Exp temperature )
        -}

test n1 = do
  putStrLn "\n\n"
  let expScore z = Exp $ z/1
  f1 <- readFile n1
  print f1
  runAlignIO
    FWlog
    EPS
    ("stmp.eps")
    f1
    (expScore 1)
    (expScore 0)
    (expScore 0)
    (Exp 1)

runAlignIO fw probFileTy probFile t1' matchSc mismatchSc indelSc temperature = do
  let f x = either error (F.forestPost . map getNewickTree) $ newicksFromText x
      t1 = f $ Text.pack t1'
  let (inn,out,zzz) = runIO t1 matchSc mismatchSc indelSc temperature
  print zzz
  let (Z:.TW (ITbl _ _ _ ift) _ :. TW (ITbl _ _ _ itt) _) = inn
  let (Z:.TW (ITbl _ _ _ oft) _ :. TW (ITbl _ _ _ ott) _) = out
  let (TreeIxL frst1 kr1 lb1 _, TreeIxL _ _ _ ub1) = bounds oft
  let ix = (TreeIxL frst1 kr1 lb1 ub1)
  let scift = ift ! ix
  let scitt = itt ! ix
  let scoft = Prelude.sum [ oft ! (TreeIxL frst1 kr1 b1 b1) | b1 <- [lb1 .. ub1] ]
  let scott = Prelude.sum [ ott ! (TreeIxL frst1 kr1 b1 b1) | b1 <- [lb1 .. ub1] ]
  print "inside"
  print scift
  print scitt
  print "outside"
  print scoft
  print scott

  let ps = map (\(k,k1) ->
            let k' = unsafeCoerce k
            in  ( k1
                , ""
                , ift!k
                , oft!k'
                , ""
                , itt!k
                , ott!k'
                , (itt!k) * (ott!k') / scift
                , {- traceShow (itt!k, ott!k') $ -} max 0 . min 1.2 $ ((itt!k) * (ott!k') / scift)
                , (maybe "-" label $ F.label t1 VG.!? k1)
                )) [ (TreeIxL frst1 kr1 (kr1 VG.! k1) (k1+1),k1) | k1 <- [0 .. ub1-1] ]
  --
  let gsc = map (\(k1,"",_,_,"",_,_,_,sc,l1) -> sc) ps
  let fillText [] = " "
      fillText xs = xs
  let gl1 = map (\k1 -> fillText . Text.unpack $ (maybe "-" label $ F.label t1 VG.!? k1)) [lb1 .. ub1 - 1]
  let gl2 = ["-"]
  print $ (ub1)
  mapM_ print ps
  print $ PA.toList oft == PA.toList ott
  case probFileTy of
         SVG -> svgGridFile probFile fw 1 ub1 gl2 gl1 gsc
         EPS -> epsGridFile probFile fw 1 ub1 gl2 gl1 gsc

