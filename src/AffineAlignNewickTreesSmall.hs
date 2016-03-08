
module Main where

import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector as V
import qualified Data.Vector.Generic as VG
import Control.Monad(forM_)
import Data.Vector.Fusion.Util
import qualified Data.Tree as T
import Debug.Trace
import Data.List (nub)

import Text.Printf
import Unsafe.Coerce
import qualified Data.Text as Text
import Numeric.Log
import Data.List (sortBy)
import Data.Ord (comparing)
import System.Console.CmdArgs
import System.Exit (exitFailure)
import System.FilePath
import Data.Char (toLower)

import ADP.Fusion
import Data.PrimitiveArray as PA hiding (map)
import FormalLanguage.CFG
import Data.Forest.Static (TreeOrder(..),Forest)
import qualified Data.Forest.Static as F
import Biobase.Newick
import Data.PrimitiveArray.Pretty.InOut

import Data.Forest.Static.ADP
import Data.Forest.Static.Node

[formalLanguage|
Verbose

Grammar: Global
N: T -- tree
N: F -- forest
N: Z -- tree for gaps
N: Q -- sibling gap mode
N: R -- parent gap mode
T: n
S: [F,F]
[F,F] -> iter    <<< [T,T] [F,F]
[F,F] -> fgap    <<< [T,Z] [Q,Q]
[F,F] -> fgap    <<< [Z,T] [Q,Q]
[Z,T] -> indel   <<< [-,n] [R,R]
[T,Z] -> delin   <<< [n,-] [R,R]
[T,T] -> align   <<< [n,n] [F,F]
[F,F] -> done    <<< [e,e]
[R,R] -> done    <<< [e,e]
[R,R] -> pgap <<< [T,T] [R,R]
[R,R] -> pgap <<< [T,Z] [R,R]
[R,R] -> pgap <<< [Z,T] [R,R]
[Q,Q] -> done    <<< [e,e]
[Q,Q] -> siter <<< [T,T] [F,F]
[Q,Q] -> sgap <<< [T,Z] [Q,Q]
[Q,Q] -> sgap <<< [Z,T] [Q,Q]
//
Outside: Labolg
Source: Global
//

Emit: Global
Emit: Labolg
|]

makeAlgebraProduct ''SigGlobal

resig :: Monad m => SigGlobal m a b c d -> SigLabolg m a b c d
resig (SigGlobal gdo git gsi gal gin gde gfg gpg gsg gh) = SigLabolg gdo git gsi gal gin gde gfg gpg gsg gh
{-# Inline resig #-}


score :: Monad m => Int -> Int -> Int -> Int -> SigGlobal m Int Int Info Info
score matchSc notmatchSc delinSc affinSc = SigGlobal -- match affine deletion 
  { gDone  = \ (Z:.():.()) -> 0 -- traceShow "EEEEEEEEEEEEE" 0
  , gIter  = \ t f -> t+f
  , gSiter  = \ t f -> t+f
  , gAlign = \ (Z:.c:.b) f -> tSI glb ("ALIGN",f,c,b) $ f + if label c == label b then matchSc else notmatchSc
  , gIndel = \ (Z:.():.b) f -> tSI glb ("INDEL",f,b) $ f
  , gDelin = \ (Z:.c:.()) f -> tSI glb ("DELIN",f,c) $ f
  , gFgap = \ t f -> tSI glb ("gap",f+t,d) $ t + f + delinSc --gap open
  , gPgap = \ t f -> tSI glb ("gap",f+t,a) $ t + f + affinSc --gap extension
  , gSgap = \ t f -> tSI glb ("gap",f+t,a) $ t + f + affinSc --gap extension
  , gH     = SM.foldl' max (-88888)
  }
{-# Inline score #-}

part :: Monad m => Log Double -> Log Double -> Log Double -> Log Double -> Log Double -> SigGlobal m (Log Double) (Log Double) Info Info
part matchSc mismatchSc delinSc affinSc temp = SigGlobal
  { gDone  = \ (Z:.():.()) -> 1
  , gIter  = \ t f -> tSI glb ("TFTFTFTFTF",t,f) $ t * f
  , gSiter  = \ t f -> tSI glb ("TFTFTFTFTF",t,f) $ t * f
  , gAlign = \ (Z:.a:.b) f -> tSI glb ("ALIGN",f,a,b) $ f * if label a == label b then matchSc * temp else mismatchSc * temp
  , gIndel = \ (Z:.():.b) f -> tSI glb ("INDEL",f,b) $ f
  , gDelin = \ (Z:.a:.()) f -> tSI glb ("DELIN",f,a) $ f
  , gFgap = \ (Z:.a:.()) f -> tSI glb ("DELIN",f,a) $ f * temp * delinSc
  , gPgap = \ (Z:.a:.()) f -> tSI glb ("DELIN",f,a) $ f * temp * affinSc
  , gSgap = \ (Z:.a:.()) f -> tSI glb ("DELIN",f,a) $ f * temp * affinSc
  , gH     = SM.foldl' (+) 0.0000001
  }
{-# Inline part #-}



type Pretty' = [[T.Tree (Info,Info)]]
pretty' :: Monad m => SigGlobal m [T.Tree (Info,Info)] [[T.Tree ((Info,Info))]] Info Info
pretty' = SigGlobal
  { gDone  = \ (Z:.():.()) -> []
  , gIter  = \ t f -> t++f
  , gSiter  = \ t f -> t++f
  , gAlign = \ (Z:.a:.b) f -> [T.Node (a,b) f]
  , gIndel = \ (Z:.():.b) f -> [T.Node (Info "-" 0,b) f]
  , gDelin = \ (Z:.a:.()) f -> [T.Node (a,Info "-" 0) f]
  , gPgap = \ t f -> t ++ f
  , gSgap = \ t f -> t ++ f
  , gFgap = \ t f -> t ++ f
  , gH     = SM.toList
  }
{-# Inline pretty' #-}



type Trix = TreeIxR Pre V.Vector Info I
type Tbl x = ITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) x
type Frst = Forest Pre V.Vector Info


--inside part
runForward :: Frst -> Frst -> Int -> Int -> Int -> Int -> Z:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int
runForward f1 f2 matchSc notmatchSc delinSc affinSc = let
                         in
                           mutateTablesDefault $
                           gGlobal (score matchSc notmatchSc delinSc affinSc) -- costs
                           (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                           (node $ F.label f1)
                           (node $ F.label f2)

-- outside part
type Trox = TreeIxR Pre V.Vector Info O
type OTbl x = ITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trox:.Trox) x


runOutside :: Frst -> Frst -> Log Double -> Log Double -> Log Double -> Log Double -> Log Double -> Z:.Tbl (Log Double):.Tbl (Log Double):.Tbl (Log Double) -> Z:.OTbl (Log Double):.OTbl (Log Double):.OTbl (Log Double)
runOutside f1 f2 matchSc mismatchSc indelSc affinSc temperature (Z:.iF:.iM:.iT)
  = mutateTablesDefault $
    gLabolg (resig (part matchSc mismatchSc indelSc affinSc temperature))
    (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    iF
    iM
    iT
    (node $ F.label f1)
    (node $ F.label f2)
{-# NoInline runOutside #-}



-- inside part
run :: Frst -> Frst -> Int -> Int -> Int -> Int -> (Z:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int:.Tbl Int,Int,Pretty')
run f1 f2 matchSc notmatchSc delinSc affinSc = (fwd,unId $ axiom a1, unId $ axiom b1)
  where fwd@(Z:.a1:.a2:.a3:.a4:.a5:.a6) = runForward f1 f2 m a d
        Z:.b1:.b2:.b3:.b4:.b5:.b6 
                    = gGlobal ((score matchSc notmatchSc delinSc affinSc) <|| pretty') 
                    (toBacktrack a1 (undefined :: Id a -> Id a)) 
                    (toBacktrack a2 (undefined :: Id a -> Id a))  
                    (toBacktrack a3 (undefined :: Id a -> Id a))  
                    (toBacktrack a4 (undefined :: Id a -> Id a))  
                    (toBacktrack a5 (undefined :: Id a -> Id a))  
                    (toBacktrack a6 (undefined :: Id a -> Id a))  
                    (node $ F.label f1) (node $ F.label f2)


-- outside part

runIO f1 f2 matchSc mismatchSc indelSc affinSc temperature = (fwd,out,unId $ axiom f)
  where fwd@(Z:.f:.m:.t) = runInside f1 f2 matchSc mismatchSc indelSc affinSc temperature
        out@(Z:.oft:.omt:.ott) = runOutside f1 f2 matchSc mismatchSc indelSc affinSc temperature fwd


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
{-
testalign m a d = do
  let t1 = f "a;" --"((d,e,f)b,(z)c)a;"  --"((b,c)e,d)a;"
      t2 = f "((c)d)a;" --"(((d,e)y,f)b,(c,(x)i)g)a;"  --"(b,(c,d)f)a;"
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
-}

-- all new from here

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
  , affinSc     :: Double
  , temperature :: Double
  }
  deriving (Show,Data,Typeable)

oOptions = Options
  { inputFiles  = def &= args
  , probFile    = def &= help "probability file prefix" -- &= explicit &= name "probfile" &= name "p" --to not guessing names 
  , probFileTy  = EPS &= help "svg, eps"
  , linearScale = False &= help "use linear, not logarithmic scaling"
  , matchSc     = 10   &= help "score for match cases, positive number"
  , notmatchSc  = -30 &= help "score for mismatches, negative number"
  , delinSc     = -10 &= help "score for deletions and insertions, negative number"
  , affinSc     = -1 &= help "score for affine gap costs, negative number"
  , temperature = 0.1 &= help "'temperature', strict (0.001) to less strict (0.99)"
  }

main :: IO ()
main = do
  o@Options{..} <- cmdArgs oOptions
  unless (length inputFiles >= 2) $ do
    putStrLn "give at least two Newick files on the command line"
    exitFailure
  let ts = init $ init $ tails inputFiles
      f  = Exp . log 
  forM_ ts $ \(n1:hs) -> do
    forM_ hs $ \n2 -> do
      putStrLn n1
      putStrLn n2
      f1 <- readFile n1
      f2 <- readFile n2
      runAlignS f1 f2 (round matchSc) (round notmatchSc) (round delinSc) (round affinSc)
      unless (null probFile) $ do
        runAlignIO (if linearScale then FWlinear else FWlog) probFileTy (probFile ++ "-" ++ takeBaseName n1 ++ "-" ++ takeBaseName n2 ++ "." ++ (map toLower $ show probFileTy)) f1 f2 (f matchSc) (f notmatchSc) (f delinSc) (f affinSc) (f temperature)




runAlignS t1' t2' matchSc notmatchSc delinSc affinSc = do
  let f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
      t1 = f $ Text.pack t1'
      t2 = f $ Text.pack t2'
  let (fwd,sc,bt') = run t1 t2 matchSc notmatchSc delinSc affinSc
  let (Z:.ITbl _ _ _ ift _ :. ITbl _ _ _ imt _ :. ITbl _ _ _ itt _) = fwd
  let bt = nub bt'
  printf "Score: %10d\n" sc
  forM_ bt $ \b -> do
    putStrLn ""
    forM_ b $ \x -> putStrLn $ T.drawTree $ fmap show x

runAlignIO fw probFileTy probFile t1' t2' matchSc mismatchSc indelSc affinSc temperature = do
  let f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
      t1 = f $ Text.pack t1'
      t2 = f $ Text.pack t2'
  let (inn,out,_) = runIO t1 t2 matchSc mismatchSc indelSc affinSc temperature -- (t2 {F.lsib = VG.fromList [-1,-1], F.rsib = VG.fromList [-1,-1]})
  let (Z:.ITbl _ _ _ ift _ :. ITbl _ _ _ imt _ :. ITbl _ _ _ itt _) = inn
  let (Z:.ITbl _ _ _ oft _ :. ITbl _ _ _ omt _ :. ITbl _ _ _ ott _) = out
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

{-
executable AffineAlignNewickTreesSmall
  if flag(examples)
    buildable:
      True
    build-depends: base
                 , ADPfusion
                 , ADPfusionForest
                 , BiobaseNewick          >= 0.0.0.1  &&  < 0.0.1.0
                 , cmdargs                >= 0.10     &&  < 0.11
                 , containers
                 , filepath
                 , ForestStructures
                 , FormalGrammars         >= 0.3      &&  < 0.4
                 , log-domain             >= 0.10     &&  < 0.11
                 , PrimitiveArray
                 , PrimitiveArray-Pretty  >= 0.0      &&  < 0.1
                 , text
                 , vector
  else
    buildable:
      False
  hs-source-dirs:
    src
  main-is:
    AffineAlignNewickTreesSmall.hs
  default-language:
    Haskell2010
  default-extensions: BangPatterns
                    , DataKinds
                    , DeriveDataTypeable
                    , FlexibleContexts
                    , GADTs
                    , MultiParamTypeClasses
                    , OverloadedStrings
                    , QuasiQuotes
                    , RecordWildCards
                    , TemplateHaskell
                    , TypeFamilies
                    , TypeOperators
  ghc-options:
    -O0
    -funbox-strict-fields
-}
