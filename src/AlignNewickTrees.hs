
module Main where

import           Control.Monad(forM_, unless)
import           Data.Char (toLower)
import           Data.List (nub, tails)
import           Data.List (sortBy)
import           Data.Ord (comparing)
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
import           System.FilePath
import           Text.Printf
import           Unsafe.Coerce

import           ADP.Fusion.Core
import           Biobase.Newick
import           Data.Forest.Static (TreeOrder(..),Forest)
import           Data.PrimitiveArray as PA hiding (map)
import           Diagrams.TwoD.ProbabilityGrid
import           FormalLanguage.CFG
import qualified Data.Forest.Static as F

import           Data.Forest.Static.AlignRL
import           Data.Forest.Static.Node



[formalLanguage|
Verbose

Grammar: Global
N: T
N: F
N: M
T: n
S: [F,F]
[F,F] -> iter  <<< [T,T] [F,F]
[F,F] -> iter  <<< [M,M] [F,F]
[T,T] -> indel <<< [-,n] [F,F]
[T,T] -> delin <<< [n,-] [F,F]
[M,M] -> align <<< [n,n] [F,F]
[F,F] -> done  <<< [e,e]
//
Outside: Labolg
Source: Global
//

Emit: Global
Emit: Labolg
|]

makeAlgebraProduct ''SigGlobal

resig :: Monad m => SigGlobal m a b c d -> SigLabolg m a b c d
resig (SigGlobal gdo git gal gin gde gh) = SigLabolg gdo git gal gin gde gh
{-# Inline resig #-}

score :: Monad m => Int -> Int -> Int -> SigGlobal m Int Int Info Info
score matchSc notmatchSc delinSc = SigGlobal
  { gDone  = \ (Z:.():.()) -> 0 -- traceShow "EEEEEEEEEEEEE" 0
  , gIter  = \ t f -> tSI glb ("TFTFTFTFTF",t,f) $ t+f
  , gAlign = \ (Z:.a:.b) f -> tSI glb ("ALIGN",f,a,b) $ f + if label a == label b then matchSc else notmatchSc
  , gIndel = \ (Z:.():.b) f -> tSI glb ("INDEL",f,b) $ f + delinSc
  , gDelin = \ (Z:.a:.()) f -> tSI glb ("DELIN",f,a) $ f + delinSc
  , gH     = SM.foldl' max (-88888)
  }
{-# Inline score #-}

part :: Monad m => Log Double -> Log Double -> Log Double -> Log Double -> SigGlobal m (Log Double) (Log Double) Info Info
part matchSc mismatchSc indelSc temp = SigGlobal
  { gDone  = \ (Z:.():.()) -> 1
  , gIter  = \ t f -> tSI glb ("TFTFTFTFTF",t,f) $ t * f
  , gAlign = \ (Z:.a:.b) f -> tSI glb ("ALIGN",f,a,b) $ f * if label a == label b then matchSc else mismatchSc
  , gIndel = \ (Z:.():.b) f -> tSI glb ("INDEL",f,b) $ f * indelSc --exp(-indelSc/temp)
  , gDelin = \ (Z:.a:.()) f -> tSI glb ("DELIN",f,a) $ f * indelSc --exp(-indelSc/temp)
  , gH     = SM.foldl' (+) 0.0000001
  }
{-# Inline part #-}

type Pretty = [[T.Tree (Info,Info)]]
pretty :: Monad m => SigGlobal m [T.Tree (Info,Info)] [[T.Tree ((Info,Info))]] Info Info
pretty = SigGlobal
  { gDone  = \ (Z:.():.()) -> []
  , gIter  = \ t f -> t++f
  , gAlign = \ (Z:.a:.b) f -> [T.Node (a,b) f]
  , gIndel = \ (Z:.():.b) f -> [T.Node (Info "-" 0,b) f]
  , gDelin = \ (Z:.a:.()) f -> [T.Node (a,Info "-" 0) f]
  , gH     = SM.toList
  }
{-# Inline pretty #-}



type Trix = TreeIxR Pre V.Vector Info I
type Tbl x = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) x
type Frst = Forest Pre V.Vector Info
type TblBt x = TwITblBt Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) Int Id Id [x]
type B = T.Tree (Info,Info)

runForward :: Frst -> Frst -> Int -> Int -> Int -> Z:.Tbl Int :.Tbl Int:.Tbl Int
runForward f1 f2 matchSc notmatchSc delinSc = mutateTablesDefault $
                   gGlobal (score matchSc notmatchSc delinSc)
                   (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                   (node $ F.label f1)
                   (node $ F.label f2)
{-# NoInline runForward #-}

runInside :: Frst -> Frst -> Log Double -> Log Double -> Log Double -> Log Double -> Z:.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double)
runInside f1 f2 matchSc mismatchSc indelSc temperature = mutateTablesDefault $
                   gGlobal (part matchSc mismatchSc indelSc temperature)
                   (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
                   (node $ F.label f1)
                   (node $ F.label f2)
{-# NoInline runInside #-}

type Trox = TreeIxR Pre V.Vector Info O
type OTbl x = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trox:.Trox) x

runOutside :: Frst -> Frst -> Log Double -> Log Double -> Log Double -> Log Double -> Z:.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double) -> Z:.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double)
runOutside f1 f2 matchSc mismatchSc indelSc temperature (Z:.iF:.iM:.iT)
  = mutateTablesDefault $
    gLabolg (resig (part matchSc mismatchSc indelSc temperature))
    (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    iF
    iM
    iT
    (node $ F.label f1)
    (node $ F.label f2)
{-# NoInline runOutside #-}

runS :: Frst -> Frst -> Int -> Int -> Int -> (Z:.Tbl Int :.Tbl Int:.Tbl Int, Int ,[[T.Tree (Info, Info)]] )
runS f1 f2 matchSc notmatchSc delinSc = (fwd,unId $ axiom f, unId $ axiom fb)
  where fwd@(Z:.f:.m:.t) = runForward f1 f2 matchSc notmatchSc delinSc
        Z:.fb:.fm:.tb = gGlobal ((score matchSc notmatchSc delinSc) <|| pretty) (toBacktrack f (undefined :: Id a -> Id a)) (toBacktrack m (undefined :: Id a -> Id a)) (toBacktrack t (undefined :: Id a -> Id a))
                        (node $ F.label f1) (node $ F.label f2)
                        :: Z:.TblBt B:.TblBt B:.TblBt B

runIO f1 f2 matchSc mismatchSc indelSc temperature = (fwd,out,unId $ axiom f)
  where fwd@(Z:.f:.m:.t) = runInside f1 f2 matchSc mismatchSc indelSc temperature
        out@(Z:.oft:.omt:.ott) = runOutside f1 f2 matchSc mismatchSc indelSc temperature fwd


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
--             (a,a)                          100
--            /     \
--       (e,-)       (d,-)                    (-3) (-3)
--      /     \
-- (b,b)       (-,f)                          100  (-5)
--            /     \
--       (c,c)       (-,d)                    100  (-5)

t11 = "a;"
t12 = "a;"
t21 = "(b,c)a;"
t22 = "(b,c)a;"
t31 = "((d,e,f)b,(z)c)a;"  --
t32 = "(((d,e)y,f)b,(c,(x)i)g)a;"  --
t41 = "d;(b)e;" -- (b,c)e;"    -- '-3'
t42 = "(d)f;b;" -- b;"
t51 = "(b:1,c:1)a:1;"
t52 = "b:2;c:2;"
t61 = "((b,c)e,d)a;"
t62 = "(b,(c,d)f)a;"
t71 = "(b)a;"
t72 = "(b)a;"

data PFT = SVG | EPS
  deriving (Show,Data,Typeable)

data Options = Options
  { inputFiles  :: [String]
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
  , probFile    = def &= help "probability file prefix" -- &= explicit &= name "probfile" &= name "p" --to not guessing names 
  , probFileTy  = EPS &= help "svg, eps; def=eps"
  , linearScale = False &= help "use linear, not logarithmic scaling; def=false"
  , matchSc     = 10  &= help "score for match cases, positive number; def=10"
  , notmatchSc  = -30 &= help "score for mismatches, negative number; def=-30"
  , delinSc     = -10 &= help "score for deletions and insertions, negative number; def=-10"
  , temperature = 0.1 &= help "'temperature', strict (0.001) to less strict (0.99); def=0.1"
  }

main :: IO ()
main = do
  o@Options{..} <- cmdArgs oOptions
  unless (length inputFiles >= 2) $ do
    putStrLn "give at least two Newick files on the command line"
    exitFailure
  let ts = init $ init $ tails inputFiles
      f z = Exp $ z/temperature 
  forM_ ts $ \(n1:hs) -> do
    forM_ hs $ \n2 -> do
      putStrLn n1
      putStrLn n2
      f1 <- readFile n1
      f2 <- readFile n2
      runAlignS f1 f2 (round matchSc) (round notmatchSc) (round delinSc)
      unless (null probFile) $ do
        runAlignIO (if linearScale then FWlinear else FWlog) probFileTy (probFile ++ "-" ++ takeBaseName n1 ++ "-" ++ takeBaseName n2 ++ "." ++ (map toLower $ show probFileTy)) f1 f2 (f matchSc) (f notmatchSc) (f delinSc) (Exp temperature)




runAlignS t1' t2' matchSc notmatchSc delinSc = do
  let f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
      t1 = f $ Text.pack t1'
      t2 = f $ Text.pack t2'
  let (fwd,sc,bt') = runS t1 t2 matchSc notmatchSc delinSc
  let (Z:.TW (ITbl _ _ _ ift) _ :. TW (ITbl _ _ _ imt) _ :. TW (ITbl _ _ _ itt) _) = fwd
  let bt = nub bt'
  printf "Score: %10d\n" sc
  forM_ bt $ \b -> do
    putStrLn ""
    forM_ b $ \x -> putStrLn $ T.drawTree $ fmap show x

runAlignIO fw probFileTy probFile t1' t2' matchSc mismatchSc indelSc temperature = do
  let f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
      t1 = f $ Text.pack t1'
      t2 = f $ Text.pack t2'
  let (inn,out,_) = runIO t1 t2 matchSc mismatchSc indelSc temperature -- (t2 {F.lsib = VG.fromList [-1,-1], F.rsib = VG.fromList [-1,-1]})
  let (Z:.TW (ITbl _ _ _ ift) _ :. TW (ITbl _ _ _ imt) _ :. TW (ITbl _ _ _ itt) _) = inn
  let (Z:.TW (ITbl _ _ _ oft) _ :. TW (ITbl _ _ _ omt) _ :. TW (ITbl _ _ _ ott) _) = out
  let (Z:.(TreeIxR frst1 lb1 _):.(TreeIxR frst2 lb2 _), Z:.(TreeIxR _ ub1 _):.(TreeIxR _ ub2 _)) = bounds oft
  let ix = (Z:.TreeIxR frst1 lb1 F:.TreeIxR frst2 lb2 F)
  let sc = ift ! ix
  let ps = map (\(k,k1,k2) ->
            let k' = unsafeCoerce k
            in  ( k1
                , k2
                , ((imt!k) * (omt!k') / sc)
                , (maybe "-" label $ F.label t1 VG.!? k1)
                , (maybe "-" label $ F.label t2 VG.!? k2)
                )) [ (Z:.TreeIxR frst1 k1 T:.TreeIxR frst2 k2 T,k1,k2) | k1 <- [lb1 .. ub1 - 1], k2 <- [lb2 .. ub2 - 1] ]
  --
  let gsc = map (\(k1,k2,sc,l1,l2) -> sc) ps
  let fillText [] = " "
      fillText xs = xs
  let gl1 = map (\k1 -> fillText . Text.unpack $ (maybe "-" label $ F.label t1 VG.!? k1)) [lb1 .. ub1 - 1]
  let gl2 = map (\k2 -> fillText . Text.unpack $ (maybe "-" label $ F.label t2 VG.!? k2)) [lb2 .. ub2 - 1]
  case probFileTy of
         SVG -> svgGridFile probFile fw ub1 ub2 gl1 gl2 gsc
         EPS -> epsGridFile probFile fw ub1 ub2 gl1 gl2 gsc
