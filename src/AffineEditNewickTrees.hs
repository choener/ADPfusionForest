
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
import qualified Diagrams.TwoD.ProbabilityGrid as PG

import           ADP.Fusion.Forest.Edit.LL



[formalLanguage|
Verbose

Grammar: Global
N: T
N: F
N: R -- extending gaps delin
N: Q -- extending gaps indel
N: E
T: r
T: x
S: [F,F]
[F,F] -> iter   <<< [F,F] [T,T]
[F,F] -> indel  <<< [Q,Q] [-,x]
[Q,Q] -> qindel <<< [Q,Q] [-,x]
[F,F] -> delin  <<< [R,R] [x,-]
[R,R] -> rdelin <<< [R,R] [x,-]
[R,R] -> iter   <<< [F,F] [T,T]
[Q,Q] -> iter   <<< [F,F] [T,T]
[T,T] -> align  <<< [F,F] [r,r]
[F,F] -> qrdone   <<< [E,E]
[Q,Q] -> qrdone   <<< [E,E]
[R,R] -> qrdone   <<< [E,E]
[E,E] -> done <<< [e,e]
//
Outside: Labolg
Source: Global
//

Emit: Global
Emit: Labolg
|]


makeAlgebraProduct ''SigGlobal



score :: Monad m => Int -> Int -> Int -> Int -> SigGlobal m Int Int Info Info Info Info
score mat not aff ndl = SigGlobal --Match notmatch affine deletion cost
  { gAlign = \ f ( Z:.n0:.n1) -> f + if label n0 == label n1 then mat else not
  , gDone = \(Z:.():.()) -> 0
  , gQrdone = \f -> f
  , gIter = \ f t -> f+t
  , gIndel = \ f (Z:.():.n1) -> f + ndl
  , gQindel = \ f (Z:.():.n1) -> f + aff
  , gDelin = \ f (Z:.n0:.()) -> f + ndl
  , gRdelin = \ f (Z:.n0:.()) -> f + aff
  , gH = SM.foldl' max (-77777) 
}
{-# Inline score #-}

resig :: Monad m => SigGlobal m a b c d e f -> SigLabolg m a b c d e f
--resig (SigGlobal gdo git gal gin gde gh) = SigLabolg gdo git gal gin gde gh
resig (SigGlobal gdo qrdo git gal gin gqin gde grde gh) = SigLabolg gdo qrdo git gal gin gqin gde grde gh
{-# Inline resig #-}


type Pretty' = [[(Info,Info)]]
pretty' :: Monad m => SigGlobal m [(Info,Info)] [[(Info,Info)]] Info Info Info Info
pretty' = SigGlobal
  { gDone  = \ (Z:.():.()) -> []
  , gQrdone  = \f -> f
  , gIter  = \ f t -> f++t
  , gAlign = \ f (Z:.a:.b) -> (a,b) : f
  , gIndel = \ f (Z:.():.b) -> (Info "-" 0,b) : f
  , gQindel = \ f (Z:.():.b) -> (Info "." 0,b) : f
  , gDelin = \ f (Z:.a:.()) -> (a,Info "-" 0) : f
  , gRdelin = \ f (Z:.a:.()) -> (a,Info "." 0) : f
  , gH     = SM.toList
  }
{-# Inline pretty' #-}


part :: Monad m => Log Double -> Log Double -> Log Double -> Log Double -> SigGlobal m (Log Double) (Log Double) Info Info Info Info
part mat not aff ndl = SigGlobal
  { gAlign = \ f ( Z:.n0:.n1) -> let z = f * if label n0 == label n1 then mat else not in {- traceShow ("align",f,n0,n1,mat,aff,z) $ -} z
  , gDone = \(Z:.():.()) -> {- traceShow ("done", 1) $ -} 1
  , gQrdone = \f -> {- traceShow ("done", 1) $ -} f
  , gIter = \ f t -> {- traceShow ("iter", f, t, f * t) $ -} f * t
  , gIndel = \ f (Z:.():.n1) -> {- traceShow ("indel", f, n1, ndl) $ -} f * ndl
  , gQindel = \ f (Z:.():.n1) -> {- traceShow ("qindel", f, n1, ndl) $ -} f * aff
  , gDelin = \ f (Z:.n0:.()) -> {- traceShow ("delin", f, n0, ndl) $ -} f * ndl
  , gRdelin = \ f (Z:.n0:.()) -> {- traceShow ("rdelin", f, n0, ndl) $ -} f * aff
  , gH = SM.foldl' (+) 0.00000
}
{-# Inline part #-}



type Trix = TreeIxL Post V.Vector Info I
type Tbl x = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) x
type TblBt x = TwITblBt Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) Int Id Id [x]
type Frst = Forest Post V.Vector Info
type B = (Info,Info)
type Trox = TreeIxL Post V.Vector Info O
type OTbl x = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trox:.Trox) x

runForward :: Int -> Int -> Int -> Int -> Frst -> Frst -> Z:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int
runForward mat not aff ndl f1 f2
  = mutateTablesDefault $
      gGlobal (score mat not aff ndl)
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
      (ITbl 0 2 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
      (ITbl 0 2 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
      (node NTroot $ F.label f1)
      (node NTroot $ F.label f2)
      (node NTany  $ F.label f1)
      (node NTany  $ F.label f2)
{-# NoInline runForward #-}

runInside :: (Log Double) -> (Log Double) -> (Log Double) -> (Log Double) -> Frst -> Frst -> Z:.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double)
runInside mat not aff ndl f1 f2
  = mutateTablesDefault $
      gGlobal (part mat not aff ndl)
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 2 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 2 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (node NTroot $ F.label f1)
      (node NTroot $ F.label f2)
      (node NTany  $ F.label f1)
      (node NTany  $ F.label f2)
{-# NoInline runInside #-}

runOutside :: (Log Double) -> (Log Double) -> (Log Double) -> (Log Double) -> Frst -> Frst -> Z:.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double) -> Z:.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double)
runOutside mat not aff ndl f1 f2 (Z:.iE:.iF:.iQ:.iR:.iT)
  = mutateTablesDefault $
      (gLabolg (resig (part mat not aff ndl)))
      (ITbl 0 2 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 2 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      iF
--      iQ --outside only uses two tables T and F, R and Q not needed
--      iR
      iT
      (node NTroot $ F.label f1)
      (node NTroot $ F.label f2)
      (node NTany  $ F.label f1)
      (node NTany  $ F.label f2)
{-# NoInline runOutside #-}


run :: Int -> Int -> Int -> Int -> Frst -> Frst -> (Z:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int,Int,Pretty')
run mat not aff ndl f1 f2 = (fwd,unId $ axiom f, unId $ axiom fb)
  where fwd@(Z:.e:.f:.q:.r:.t) = runForward mat not aff ndl f1 f2
        Z:.eb:.fb:.qb:.rb:.tb = gGlobal (score mat not aff ndl <|| pretty')
                          (toBacktrack e (undefined :: Id a -> Id a))
                          (toBacktrack f (undefined :: Id a -> Id a))
                          (toBacktrack q (undefined :: Id a -> Id a))
                          (toBacktrack r (undefined :: Id a -> Id a))
                          (toBacktrack t (undefined :: Id a -> Id a))  
                          (node NTroot $ F.label f1) (node NTroot $ F.label f2)
                          (node NTany  $ F.label f1) (node NTany  $ F.label f2)
         :: Z:.TblBt B:.TblBt B:.TblBt B:.TblBt B:.TblBt B
{-# NoInline run #-}

runIO f1 f2 matchSc notmatchSc affineSc indelSc temperature = (fwd,out,unId $ axiom f)
  where fwd@(Z:.e:.f:.q:.r:.t) = runInside matchSc notmatchSc affineSc indelSc f1 f2
        out@(Z:.oet:.oft:.oqt:.ort:.ott) = runOutside matchSc notmatchSc affineSc indelSc f1 f2 fwd
{-# NoInline runIO #-}



data PFT = SVG | EPS
  deriving (Show,Data,Typeable)


data Options = Options
  { inputFiles  :: [String]
  , probFile    :: String
  , probFileTy  :: PFT
  , linearScale :: Bool
  , matchSc     :: Double
  , notmatchSc  :: Double
  , affineSc    :: Double
  , delinSc     :: Double
  , temperature :: Double
  }
  deriving (Show,Data,Typeable)

oOptions = Options
  { inputFiles  = def &= args
  , matchSc     = 10  &= help "score for match cases, positive number; def=10"
  , notmatchSc = -30 &= help "score for mismatches, negative number; def=-30"
  , affineSc  = -1 &= help "score for affine costs, negative number; def=-30"
  , delinSc     = -10 &= help "score for deletions and insertions, negative number; def=-10"
  , probFile = def
  , probFileTy = EPS
  , linearScale = False
  , temperature = 1
  }

main :: IO ()
main = do
  o@Options{..} <- cmdArgs oOptions
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
      let (_,sc,bt') = run (round matchSc) (round notmatchSc) (round affineSc) (round delinSc) (fff f1) (fff f2)
      let bt = nub $ take 10 bt'
      printf "Score: %10d\n" sc
      putStrLn ""
      forM_ bt $ \b -> do
        forM_ b $ \(Info l _, Info r _) -> printf "%1s.%1s  " (Text.unpack l) (Text.unpack r)
        putStrLn ""
      unless (null probFile) $ do
        runAlignIO (if linearScale then PG.FWlinear else PG.FWlog) probFileTy (probFile ++ "-" ++ takeBaseName n1 ++ "-" ++ takeBaseName n2 ++ "." ++ (map toLower $ show probFileTy)) f1 f2 (expScore matchSc) (expScore notmatchSc) (expScore affineSc) (expScore delinSc) (Exp temperature )

runAlignIO fw probFileTy probFile t1' t2' matchSc notmatchSc affineSc indelSc temperature = do
  let f x = either error (F.forestPost . map getNewickTree) $ newicksFromText x
      t1 = f $ Text.pack t1'
      t2 = f $ Text.pack t2'
  let (inn,out,zzz) = runIO t1 t2 matchSc notmatchSc affineSc indelSc temperature -- (t2 {F.lsib = VG.fromList [-1,-1], F.rsib = VG.fromList [-1,-1]})
--  print zzz
  let (Z:.TW (ITbl _ _ _ iet) _:.TW (ITbl _ _ _ ift) _ :. TW (ITbl _ _ _ iqt) _ :. TW (ITbl _ _ _ irt) _ :. TW (ITbl _ _ _ itt) _) = inn
  let (Z:.TW (ITbl _ _ _ oet) _:.TW (ITbl _ _ _ oft) _ :. TW (ITbl _ _ _ oqt) _ :. TW (ITbl _ _ _ ort) _ :. TW (ITbl _ _ _ ott) _) = out
  let (Z:.(TreeIxL frst1 kr1 lb1 _):.(TreeIxL frst2 kr2 lb2 _), Z:.(TreeIxL _ _ _ ub1):.(TreeIxL _ _ _ ub2)) = bounds oft
  let ix = (Z:.TreeIxL frst1 kr1 lb1 ub1:.TreeIxL frst2 kr2 lb2 ub2)
  let scift = ift ! ix
  let scitt = itt ! ix
  let scoft = Prelude.sum [ oft ! (Z:.TreeIxL frst1 kr1 b1 b1 :. TreeIxL frst2 kr2 b2 b2) | b1 <- [lb1 .. ub1], b2 <- [lb2 .. ub2] ]
  let scott = Prelude.sum [ ott ! (Z:.TreeIxL frst1 kr1 b1 b1 :. TreeIxL frst2 kr2 b2 b2) | b1 <- [lb1 .. ub1], b2 <- [lb2 .. ub2] ]
  print "inside"
  print scift
  print scitt
  print "outside"
  print scoft
  print scott

  let ps = map (\(k,k1,k2) ->
            let k' = unsafeCoerce k
            in  ( k1
                , k2
                , ""
                , ift!k
                , oft!k'
                , ""
                , itt!k
                , ott!k'
                , (itt!k) * (ott!k') / scift
                , {- traceShow (itt!k, ott!k') $ -} max 0 . min 1.2 $ ((itt!k) * (ott!k') / scift)
                , (maybe "-" label $ F.label t1 VG.!? k1)
                , (maybe "-" label $ F.label t2 VG.!? k2)
                )) [ (Z:.TreeIxL frst1 kr1 (kr1 VG.! k1) (k1+1) :.TreeIxL frst2 kr2 (kr2 VG.! k2) (k2+1),k1,k2) | k1 <- [0 .. ub1-1], k2 <- [0 .. ub2-1] ]
  --
  let gsc = map (\(k1,k2,"",_,_,"",_,_,_,sc,l1,l2) -> sc) ps
  let fillText [] = " "
      fillText xs = xs
  let gl1 = map (\k1 -> fillText . Text.unpack $ (maybe "-" label $ F.label t1 VG.!? k1)) [lb1 .. ub1 - 1]
  let gl2 = map (\k2 -> fillText . Text.unpack $ (maybe "-" label $ F.label t2 VG.!? k2)) [lb2 .. ub2 - 1]
  case probFileTy of
         SVG -> PG.svgGridFile probFile fw ub1 ub2 gl1 gl2 gsc
         EPS -> PG.epsGridFile probFile fw ub1 ub2 gl1 gl2 gsc

