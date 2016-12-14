
module Main where


import           Data.Char (toLower)
import           System.FilePath
import           Control.Monad(forM_,unless)
import           Data.List (nub,tails)
import           Data.Text (Text)
import           Numeric.Log
import qualified Data.Text as Text
import           System.Console.CmdArgs
import           System.Exit (exitFailure)
import           Text.Printf
import           Unsafe.Coerce

import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Data.Tree as T
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Generic as VG

import           ADP.Fusion.Core
import           Biobase.Newick
import           Data.Forest.Static (TreeOrder(..),Forest)
import           Data.PrimitiveArray as PA hiding (map)
import           FormalLanguage.CFG
import qualified Data.Forest.Static as F
import           Diagrams.TwoD.ProbabilityGrid

import           ADP.Fusion.Forest.Align.RL






-- grammar for affine gap costs with explicit affine gaps

[formalLanguage|
Verbose

Grammar: Global
N: T -- tree
N: F -- forest
N: Z -- tree for gaps
N: Y -- tree for affine gaps
N: P -- parent gap mode
N: G -- sibling gap together with P
T: n
S: [F,F]
[F,F] -> iter    <<< [T,T] [F,F]
[F,F] -> iter    <<< [T,Z] [F,G]
[F,F] -> iter    <<< [Z,T] [G,F]
[F,F] -> done    <<< [e,e]
[P,F] -> pfalign <<< [T,T] [P,F]
[P,F] -> pfdelin <<< [T,Z] [P,G]
[P,F] -> pfindel <<< [Y,T] [P,F]
[P,F] -> alldone <<< [F,F]
[F,P] -> alldone <<< [F,F]
[F,P] -> fpalign <<< [T,T] [F,P]
[F,P] -> fpdelin <<< [T,Y] [F,P]
[F,P] -> fpindel <<< [Z,T] [G,P]
[G,F] -> gfalign <<< [T,T] [G,F]
[G,F] -> gfdelin <<< [T,Z] [P,G]
[G,F] -> gfindel <<< [Y,T] [G,F]
[G,F] -> alldone <<< [F,F]
[F,G] -> alldone <<< [F,F]
[F,G] -> fgalign <<< [T,T] [F,F]
[F,G] -> fgdelin <<< [T,Y] [F,G]
[F,G] -> fgindel <<< [Z,T] [G,P]
[G,P] -> gpalign <<< [T,T] [F,P]
[G,P] -> gpdelin <<< [T,Y] [F,P]
[G,P] -> gpindel <<< [Y,T] [G,P]
[P,G] -> pgalign <<< [T,T] [P,F]
[P,G] -> pgdelin <<< [T,Y] [P,G]
[P,G] -> pgindel <<< [Y,T] [P,F]
[T,T] -> align   <<< [n,n] [F,F]
[Z,T] -> indel   <<< [-,n] [P,F]
[T,Z] -> delin   <<< [n,-] [F,P]
[Y,T] -> afindel <<< [-,n] [P,F]
[T,Y] -> afdelin <<< [n,-] [F,P]
//
Outside: Labolg
Source: Global
//
Emit: Global
Emit: Labolg
|]

makeAlgebraProduct ''SigGlobal

score :: Monad m => Int -> Int -> Int -> SigGlobal m Int Int Info Info
score m a d = SigGlobal -- Match Affine Deletion costs 
  { gDone  = \ (Z:.():.()) -> 0
  , gIter  = \ t f -> tSI glb ("TFTFTFTFTF",t,f) $ t+f
  , gAlign = \ (Z:.c:.b) f -> tSI glb ("ALIGN",f,c,b) $ f + if label c == label b then m else - 100
  , gIndel = \ (Z:.():.b) f -> tSI glb ("INDEL",f,b) $ f + d --gap open
  , gDelin = \ (Z:.c:.()) f -> tSI glb ("DELIN",f,c) $ f + d --gap open
  , gAfdelin = \ (Z:.c:.()) f -> tSI glb ("AFDELIN",f,c) $ f + a --gap extension
  , gAfindel = \ (Z:.():.b) f -> tSI glb ("AFINDEL",f,b) $ f + a --gap extension
  , gFpalign = \ t f -> t + f
  , gPfalign = \ t f -> t + f
  , gGpalign = \ t f -> t + f
  , gPgalign = \ t f -> t + f
  , gGfalign = \ t f -> t + f
  , gFgalign = \ t f -> t + f
  , gFpdelin = \ t f -> t + f
  , gPfdelin = \ t f -> t + f
  , gPgdelin = \ t f -> t + f
  , gGpdelin = \ t f -> t + f
  , gFgdelin = \ t f -> t + f
  , gGfdelin = \ t f -> t + f
  , gFpindel = \ t f -> t + f
  , gPfindel = \ t f -> t + f
  , gFgindel = \ t f -> t + f
  , gGfindel = \ t f -> t + f
  , gPgindel = \ t f -> t + f
  , gGpindel = \ t f -> t + f
  , gAlldone = \ f -> f
  , gH       = SM.foldl' max (-88888)
  }
{-# Inline score #-}


resig :: Monad m => SigGlobal m a b c d -> SigLabolg m a b c d
resig (SigGlobal gdo git gal gin gde gaf gaf2 gfp gpf ggp gpg ggf gfg gfp2 gpf2 gpg2 ggp2 gfg2 ggf2 gfp3 gpf3 gfg3 ggf3 gpg3 ggp3 gal2 gh)
  = SigLabolg gdo git gal gin gde gaf gaf2 gfp gpf ggp gpg ggf gfg gfp2 gpf2 gpg2 ggp2 gfg2 ggf2 gfp3 gpf3 gfg3 ggf3 gpg3 ggp3 gal2 gh
{-# Inline resig #-}


type Pretty' = [[T.Tree (Info,Info)]]
pretty' :: Monad m => SigGlobal m [T.Tree (Info,Info)] [[T.Tree ((Info,Info))]] Info Info
pretty' = SigGlobal
  { gDone  = \ (Z:.():.()) -> []
  , gIter  = \ t f -> t++f
  , gAlign = \ (Z:.a:.b) f -> [T.Node (a,b) f]
  , gIndel = \ (Z:.():.b) f -> [T.Node (Info "-" 0,b) f]
  , gDelin = \ (Z:.a:.()) f -> [T.Node (a,Info "-" 0) f]
  , gAfdelin = \ (Z:.a:.()) f -> [T.Node (a,Info "." 0) f]
  , gAfindel = \ (Z:.():.b) f -> [T.Node (Info "." 0,b) f]
  , gFpalign = \ t f -> t ++ f
  , gPfalign = \ t f -> t ++ f
  , gGpalign = \ t f -> t ++ f
  , gPgalign = \ t f -> t ++ f
  , gGfalign = \ t f -> t ++ f
  , gFgalign = \ t f -> t ++ f
  , gFpdelin = \ t f -> t ++ f
  , gPfdelin = \ t f -> t ++ f
  , gPgdelin = \ t f -> t ++ f
  , gGpdelin = \ t f -> t ++ f
  , gFgdelin = \ t f -> t ++ f
  , gGfdelin = \ t f -> t ++ f
  , gFpindel = \ t f -> t ++ f
  , gPfindel = \ t f -> t ++ f
  , gFgindel = \ t f -> t ++ f
  , gGfindel = \ t f -> t ++ f
  , gPgindel = \ t f -> t ++ f
  , gGpindel = \ t f -> t ++ f
  , gAlldone = \ f -> f
  , gH       = SM.toList
  }
{-# Inline pretty' #-}



part :: Monad m => Log Double -> Log Double -> Log Double -> SigGlobal m (Log Double) (Log Double) Info Info
part mat aff ndl = SigGlobal
  { gDone  = \ (Z:.():.()) -> 1
  , gIter  = \ t f -> t*f
  , gAlign = \ (Z:.a:.b) f -> let z = f * if label a == label b then mat else -100 in  z
  , gIndel = \ (Z:.():.b) f -> f * ndl
  , gDelin = \ (Z:.a:.()) f -> f * ndl
  , gAfdelin = \ (Z:.a:.()) f -> f * aff
  , gAfindel = \ (Z:.():.b) f -> f * aff
  , gFpalign = \ t f -> t * f
  , gPfalign = \ t f -> t * f
  , gGpalign = \ t f -> t * f
  , gPgalign = \ t f -> t * f
  , gGfalign = \ t f -> t * f
  , gFgalign = \ t f -> t * f
  , gFpdelin = \ t f -> t * f
  , gPfdelin = \ t f -> t * f
  , gPgdelin = \ t f -> t * f
  , gGpdelin = \ t f -> t * f
  , gFgdelin = \ t f -> t * f
  , gGfdelin = \ t f -> t * f
  , gFpindel = \ t f -> t * f
  , gPfindel = \ t f -> t * f
  , gFgindel = \ t f -> t * f
  , gGfindel = \ t f -> t * f
  , gPgindel = \ t f -> t * f
  , gGpindel = \ t f -> t * f
  , gAlldone = \ f -> f
  , gH       = SM.foldl' (+) 0.00000
  }
{-# Inline part #-}




type Trix = TreeIxR Pre V.Vector Info I
type Tbl x = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) x
type TblBt x = TwITblBt Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) Int Id Id [x]
type Frst = Forest Pre V.Vector Info
--type B = (Info,Info)
type Trox = TreeIxR Pre V.Vector Info O
type OTbl x = TwITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trox:.Trox) x

runForward :: Frst -> Frst -> Int -> Int -> Int -> Z:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int
runForward f1 f2 m a d = let
                         in
                           mutateTablesDefault $
                           gGlobal (score m a d) -- costs
                           (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (node NTany $ F.label f1)
                           (node NTany $ F.label f2)
{-# NoInline runForward #-}



runInside :: (Log Double) -> (Log Double) -> (Log Double) -> Frst -> Frst -> Z:.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double)
runInside mat aff ndl f1 f2
  = mutateTablesDefault $
      gGlobal (part mat aff ndl)
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (node NTany  $ F.label f1)
      (node NTany  $ F.label f2)
{-# NoInline runInside #-}



runOutside :: (Log Double) -> (Log Double) -> (Log Double) -> Frst -> Frst -> Z:.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double) :.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double) -> Z:.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double)
runOutside mat aff ndl f1 f2 (Z:.iF:.iT:.iP:.iG:.iY:.iZ:.iF2:.iT2:.iP2:.iG2:.iY2:.iZ2)
  = mutateTablesDefault $
      (gLabolg (resig (part mat aff ndl)))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) 0 [] ))
      iF
      iT
      iG
      iP
      iY
      iZ
      iF2
      iT2
      iG2
      iP2
      iY2
      iZ2
      (node NTany  $ F.label f1)
      (node NTany  $ F.label f2)
{-# NoInline runOutside #-}





type B = T.Tree (Info,Info)

run :: Frst -> Frst -> Int -> Int -> Int -> (Z:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int,Int,Pretty')
run f1 f2 m a d = (fwd,unId $ axiom a1, unId $ axiom b1)
  where fwd@(Z:.a1:.a2:.a3:.a4:.a5:.a6:.a7:.a8:.a9:.a10:.a11:.a12) = runForward f1 f2 m a d
        Z:.b1:.b2:.b3:.b4:.b5:.b6:.b7:.b8:.b9:.b10:.b11:.b12 
                    = gGlobal ((score m a d) <|| pretty') 
                    (toBacktrack a1 (undefined :: Id a -> Id a)) 
                    (toBacktrack a2 (undefined :: Id a -> Id a))  
                    (toBacktrack a3 (undefined :: Id a -> Id a))  
                    (toBacktrack a4 (undefined :: Id a -> Id a))  
                    (toBacktrack a5 (undefined :: Id a -> Id a))  
                    (toBacktrack a6 (undefined :: Id a -> Id a))  
                    (toBacktrack a7 (undefined :: Id a -> Id a))  
                    (toBacktrack a8 (undefined :: Id a -> Id a))  
                    (toBacktrack a9 (undefined :: Id a -> Id a))  
                    (toBacktrack a10 (undefined :: Id a -> Id a))  
                    (toBacktrack a11 (undefined :: Id a -> Id a))  
                    (toBacktrack a12 (undefined :: Id a -> Id a))  
                    (node NTany $ F.label f1) (node NTany $ F.label f2)
          :: Z:.TblBt B:.TblBt B:.TblBt B:.TblBt B:.TblBt B:.TblBt B:.TblBt B:.TblBt B:.TblBt B:.TblBt B:.TblBt B:.TblBt B


runIO f1 f2 matchSc affineSc indelSc temperature = (fwd,out,unId $ axiom f)
  where fwd@(Z:.f:.t:.p:.g:.y:.z:.fa:.ta:.pa:.ga:.ya:.za) = runInside matchSc affineSc indelSc f1 f2
        out@(Z:.oft:.ott:.opt:.ogt:.oyt:.ozt:.ofta:.otta:.opta:.ogta:.oyta:.ozta) = runOutside matchSc affineSc indelSc f1 f2 fwd
{-# NoInline runIO #-}



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

testalign m a d = do
  let t1 = f  "(b,c,d)a;" --"((d,e,f)b,(z)c)a;"  --"((b,c)e,d)a;"
      t2 = f  "(d)a;" --"(((d,e)y,f)b,(c,(x)i)g)a;"  --"(b,(c,d)f)a;"
--  let t1 = f "d;(b)e;" -- (b,c)e;"    -- '-3'
--      t2 = f "(d)f;b;" -- b;"
--  let t1 = f "(b:1,c:1)a:1;"
--      t2 = f "b:2;c:2;"
      f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
  print t1
  putStrLn ""
  print t2
  putStrLn ""
  let (_,sc,bt') = run t1 t2 m a d -- (t2 {F.lsib = VG.fromList [-1,-1], F.rsib = VG.fromList [-1,-1]})
 -- mapM_ print $ assocs f
  print ""
 -- mapM_ print $ assocs t
  --print f
  --print t
  let bt = take 10 $ nub bt'
  print (length bt', length bt)
  forM_ bt $ \b -> do
    putStrLn ""
    forM_ b $ \x -> putStrLn $ T.drawTree $ fmap show x
  print sc


--main :: IO ()
--main = return ()

data PFT = SVG | EPS
  deriving (Show,Data,Typeable)


data Options = Options
  { inputFiles  :: [String]
  , probFile    :: String
  , probFileTy  :: PFT
  , linearScale :: Bool
  , matchSc     :: Double
  , affineSc  :: Double
  , delinSc     :: Double
  , temperature :: Double
  }
  deriving (Show,Data,Typeable)

oOptions = Options
  { inputFiles  = def &= args
  , matchSc     = 10  &= help "score for match cases, positive number; def=10"
  , affineSc  = -30 &= help "score for affine costs, negative number; def=-30"
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
      f z = Exp $ z/temperature 
  forM_ ts $ \(n1:hs) -> do
    forM_ hs $ \n2 -> do
      putStrLn n1
      putStrLn n2
      f1 <- readFile n1
      f2 <- readFile n2
      runAlignS f1 f2 (round matchSc) (round affineSc) (round delinSc)
      unless (null probFile) $ do
        runAlignIO (if linearScale then FWlinear else FWlog) probFileTy (probFile ++ "-" ++ takeBaseName n1 ++ "-" ++ takeBaseName n2 ++ "." ++ (map toLower $ show probFileTy)) f1 f2 (f matchSc) (f affineSc) (f delinSc) (Exp temperature)




runAlignS t1' t2' matchSc affineSc delinSc = do
  let f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
      t1 = f $ Text.pack t1'
      t2 = f $ Text.pack t2'
  let (fwd,sc,bt') = run t1 t2 matchSc affineSc delinSc
  let (Z:.TW (ITbl _ _ _ ift) _ :. TW (ITbl _ _ _ itt) _ :. TW (ITbl _ _ _ igt) _ :. TW (ITbl _ _ _ ipt) _ :. TW (ITbl _ _ _ iyt) _ :. TW (ITbl _ _ _ izt) _ :.TW (ITbl _ _ _ ift2) _ :. TW (ITbl _ _ _ itt2) _ :. TW (ITbl _ _ _ igt2) _ :. TW (ITbl _ _ _ ipt2) _ :. TW (ITbl _ _ _ iyt2) _ :. TW (ITbl _ _ _ izt2) _) = fwd
  let bt = nub bt'
  printf "Score: %10d\n" sc
  forM_ bt $ \b -> do
    putStrLn ""
    forM_ b $ \x -> putStrLn $ T.drawTree $ fmap show x

runAlignIO fw probFileTy probFile t1' t2' matchSc affineSc indelSc temperature = do
  let f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
      t1 = f $ Text.pack t1'
      t2 = f $ Text.pack t2'
  let (inn,out,_) = runIO t1 t2 matchSc affineSc indelSc temperature -- (t2 {F.lsib = VG.fromList [-1,-1], F.rsib = VG.fromList [-1,-1]})
  let (Z:.TW (ITbl _ _ _ ift) _ :. TW (ITbl _ _ _ itt) _ :. TW (ITbl _ _ _ ipt) _ :. TW (ITbl _ _ _ igt) _ :. TW (ITbl _ _ _ iyt) _ :. TW (ITbl _ _ _ izt) _ :.TW (ITbl _ _ _ ift2) _ :. TW (ITbl _ _ _ itt2) _ :. TW (ITbl _ _ _ ipt2) _ :. TW (ITbl _ _ _ igt2) _ :. TW (ITbl _ _ _ iyt2) _ :. TW (ITbl _ _ _ izt2) _) = inn
  let (Z:.TW (ITbl _ _ _ oft) _ :. TW (ITbl _ _ _ ott) _ :. TW (ITbl _ _ _ opt) _ :. TW (ITbl _ _ _ ogt) _ :. TW (ITbl _ _ _ oyt) _ :. TW (ITbl _ _ _ ozt) _ :.TW (ITbl _ _ _ oft2) _ :. TW (ITbl _ _ _ ott2) _ :. TW (ITbl _ _ _ opt2) _ :. TW (ITbl _ _ _ ogt2) _ :. TW (ITbl _ _ _ oyt2) _ :. TW (ITbl _ _ _ ozt2) _) = out
  let (Z:.(TreeIxR frst1 lb1 _):.(TreeIxR frst2 lb2 _), Z:.(TreeIxR _ ub1 _):.(TreeIxR _ ub2 _)) = bounds oft
  let ix = (Z:.TreeIxR frst1 lb1 F:.TreeIxR frst2 lb2 F)
  let scift = ift ! ix
  print scift
  let scoft = Prelude.sum [ oft ! (Z:.TreeIxR frst1 b1 F :. TreeIxR frst2 b2 F) | b1 <- [lb1 .. ub1], b2 <- [lb2 .. ub2] ]
  print scoft
  let scitt = Prelude.sum [ itt ! (Z:.TreeIxR frst1 b1 T :. TreeIxR frst2 b2 T) | b1 <- [lb1 .. ub1], b2 <- [lb2 .. ub2] ]
  print scitt
  let scott = Prelude.sum [ ott ! (Z:.TreeIxR frst1 b1 T :. TreeIxR frst2 b2 T) | b1 <- [lb1 .. ub1], b2 <- [lb2 .. ub2] ]
  print scott
  let ps = map (\(k,k1,k2) ->
            let k' = unsafeCoerce k
            in  ( k1
                , k2
                , ((itt!k) * (ott!k') / scift)
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









-- part copied from tree edit
{-
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
      let t1 = f $ Text.pack t1'
      let t2 = f $ Text.pack t2'
      let (_,sc,bt') = run (round matchSc) (round affineSc) (round delinSc) (t1) (t2)
      let bt = nub $ take 10 bt'
      printf "Score: %10d\n" sc
      putStrLn ""
      forM_ bt $ \b -> do
        forM_ b $ \(Info l _, Info r _) -> printf "%1s.%1s  " (Text.unpack l) (Text.unpack r)
        putStrLn ""
      unless (null probFile) $ do
        runAlignIO (if linearScale then FWlinear else FWlog) probFileTy (probFile ++ "-" ++ takeBaseName n1 ++ "-" ++ takeBaseName n2 ++ "." ++ (map toLower $ show probFileTy)) f1 f2 (expScore matchSc) (expScore affineSc) (expScore delinSc) (Exp temperature )

runAlignIO fw probFileTy probFile t1' t2' matchSc affineSc indelSc temperature = do
  let f x = either error (F.forestPost . map getNewickTree) $ newicksFromText x
      t1 = f $ Text.pack t1'
      t2 = f $ Text.pack t2'
  let (inn,out,zzz) = runIO t1 t2 matchSc affineSc indelSc temperature -- (t2 {F.lsib = VG.fromList [-1,-1], F.rsib = VG.fromList [-1,-1]})
--  print zzz
  let (Z:.TW (ITbl _ _ _ ift) _ :. TW (ITbl _ _ _ itt) _ :. TW (ITbl _ _ _ itq) _ :. TW (ITbl _ _ _ itr) _) = inn
  let (Z:.TW (ITbl _ _ _ oft) _ :. TW (ITbl _ _ _ ott) _ :. TW (ITbl _ _ _ otq) _ :. TW (ITbl _ _ _ otr) _) = out
  let (Z:.(TreeIxR frst1 kr1 lb1 _):.(TreeIxR frst2 kr2 lb2 _), Z:.(TreeIxR _ _ _ ub1):.(TreeIxR _ _ _ ub2)) = bounds oft
  let ix = (Z:.TreeIxR frst1 kr1 lb1 ub1:.TreeIxR frst2 kr2 lb2 ub2)
  let scift = ift ! ix
  let scitt = itt ! ix
  let scoft = Prelude.sum [ oft ! (Z:.TreeIxR frst1 kr1 b1 b1 :. TreeIxR frst2 kr2 b2 b2) | b1 <- [lb1 .. ub1], b2 <- [lb2 .. ub2] ]
  let scott = Prelude.sum [ ott ! (Z:.TreeIxR frst1 kr1 b1 b1 :. TreeIxR frst2 kr2 b2 b2) | b1 <- [lb1 .. ub1], b2 <- [lb2 .. ub2] ]
--  print "inside"
--  print scift
--  print scitt
--  print "outside"
--  print scoft
--  print scott

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
                )) [ (Z:.TreeIxR frst1 kr1 (kr1 VG.! k1) (k1+1) :.TreeIxR frst2 kr2 (kr2 VG.! k2) (k2+1),k1,k2) | k1 <- [0 .. ub1-1], k2 <- [0 .. ub2-1] ]
  --
  let gsc = map (\(k1,k2,"",_,_,"",_,_,_,sc,l1,l2) -> sc) ps
  let fillText [] = " "
      fillText xs = xs
  let gl1 = map (\k1 -> fillText . Text.unpack $ (maybe "-" label $ F.label t1 VG.!? k1)) [lb1 .. ub1 - 1]
  let gl2 = map (\k2 -> fillText . Text.unpack $ (maybe "-" label $ F.label t2 VG.!? k2)) [lb2 .. ub2 - 1]
  case probFileTy of
         SVG -> svgGridFile probFile fw ub1 ub2 gl1 gl2 gsc
         EPS -> epsGridFile probFile fw ub1 ub2 gl1 gl2 gsc

-}