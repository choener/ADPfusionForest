
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

import ADP.Fusion
import Data.PrimitiveArray as PA hiding (map)
import FormalLanguage.CFG
import Data.Forest.Static (TreeOrder(..),Forest)
import qualified Data.Forest.Static as F
import Biobase.Newick

import Data.Forest.Static.ADP
import Data.Forest.Static.Node

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

score :: Monad m => SigGlobal m Double Double Info Info
score = SigGlobal
  { gDone  = \ (Z:.():.()) -> 0 -- traceShow "EEEEEEEEEEEEE" 0
  , gIter  = \ t f -> tSI glb ("TFTFTFTFTF",t,f) $ t+f
  , gAlign = \ (Z:.a:.b) f -> tSI glb ("ALIGN",f,a,b) $ f + if label a == label b then 100 else -11
  , gIndel = \ (Z:.():.b) f -> tSI glb ("INDEL",f,b) $ f - 5
  , gDelin = \ (Z:.a:.()) f -> tSI glb ("DELIN",f,a) $ f - 3
  , gH     = SM.foldl' max (-88888)
  }
{-# Inline score #-}

part :: Monad m => SigGlobal m Double Double Info Info
part = SigGlobal
  { gDone  = \ (Z:.():.()) -> 1
  , gIter  = \ t f -> tSI glb ("TFTFTFTFTF",t,f) $ t*f
  , gAlign = \ (Z:.a:.b) f -> tSI glb ("ALIGN",f,a,b) $ f * if label a == label b then 1 else 0.1
  , gIndel = \ (Z:.():.b) f -> tSI glb ("INDEL",f,b) $ f * 0.1
  , gDelin = \ (Z:.a:.()) f -> tSI glb ("DELIN",f,a) $ f * 0.1
  , gH     = SM.foldl' (+) 0
  }
{-# Inline part #-}

{-
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
type Tbl x = ITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) x
type Frst = Forest Pre V.Vector Info

runForward :: Frst -> Frst -> Z:.Tbl Double:.Tbl Double:.Tbl Double
runForward f1 f2 = mutateTablesDefault $
                   gGlobal score
                   (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (-99999) [] ))
                   (node $ F.label f1)
                   (node $ F.label f2)
{-# NoInline runForward #-}

runInside :: Frst -> Frst -> Z:.Tbl Double:.Tbl Double:.Tbl Double
runInside f1 f2 = mutateTablesDefault $
                   gGlobal part
                   (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
                   (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
                   (node $ F.label f1)
                   (node $ F.label f2)
{-# NoInline runInside #-}

type Trox = TreeIxR Pre V.Vector Info O
type OTbl x = ITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trox:.Trox) x

runOutside :: Frst -> Frst -> Z:.Tbl Double:.Tbl Double:.Tbl Double -> Z:.OTbl Double:.OTbl Double:.OTbl Double
runOutside f1 f2 (Z:.iF:.iM:.iT)
  = mutateTablesDefault $
    gLabolg (resig part)
    (ITbl 0 0 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    (ITbl 0 1 (Z:.EmptyOk:.EmptyOk) (PA.fromAssocs (Z:.minIx f1:.minIx f2) (Z:.maxIx f1:.maxIx f2) (0) [] ))
    iF
    iM
    iT
    (node $ F.label f1)
    (node $ F.label f2)
{-# NoInline runOutside #-}


runS f1 f2 = (fwd,unId $ axiom f, unId $ axiom fb)
  where fwd@(Z:.f:.m:.t) = runForward f1 f2
        Z:.fb:.fm:.tb = gGlobal (score <|| pretty) (toBacktrack f (undefined :: Id a -> Id a)) (toBacktrack m (undefined :: Id a -> Id a)) (toBacktrack t (undefined :: Id a -> Id a))
                        (node $ F.label f1) (node $ F.label f2)

runIO f1 f2 = (fwd,out,unId $ axiom f)
  where fwd@(Z:.f:.m:.t) = runInside f1 f2
        out@(Z:.oft:.omt:.ott) = runOutside f1 f2 fwd


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

testalignS t1' t2' = do
  let f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
      t1 = f $ Text.pack t1'
      t2 = f $ Text.pack t2'
  print t1
  putStrLn ""
  print t2
  putStrLn ""
  let (fwd,sc,bt') = runS t1 t2
  let (Z:.ITbl _ _ _ ift _ :. ITbl _ _ _ imt _ :. ITbl _ _ _ itt _) = fwd
  print ""
  let bt = take 10 $ nub bt'
  print (length bt', length bt)
  forM_ bt $ \b -> do
    putStrLn ""
    forM_ b $ \x -> putStrLn $ T.drawTree $ fmap show x
  print sc

testalignIO t1' t2' = do
  let f x = either error (F.forestPre . map getNewickTree) $ newicksFromText x
      t1 = f $ Text.pack t1'
      t2 = f $ Text.pack t2'
  print t1
  putStrLn ""
  print t2
  putStrLn ""
  let (inn,out,_) = runIO t1 t2 -- (t2 {F.lsib = VG.fromList [-1,-1], F.rsib = VG.fromList [-1,-1]})
  let (Z:.ITbl _ _ _ ift _ :. ITbl _ _ _ imt _ :. ITbl _ _ _ itt _) = inn
  let (Z:.ITbl _ _ _ oft _ :. ITbl _ _ _ omt _ :. ITbl _ _ _ ott _) = out
  let (Z:.(TreeIxR frst1 lb1 _):.(TreeIxR frst2 lb2 _), Z:.(TreeIxR _ ub1 _):.(TreeIxR _ ub2 _)) = bounds oft
  let ix = (Z:.TreeIxR frst1 lb1 F:.TreeIxR frst2 lb2 F)
  let sc = ift ! ix
  printf "%30s %10s %10s %10s\n" ("index"::String) ("i-F"::String) ("i-M"::String) ("i-T"::String)
  mapM_ (\(k,v) -> printf "%30s %10.2f %10.2f %10.2f\n" (show k) v (imt ! k) (itt ! k)) $ assocs ift
  print (ix,sc)
  printf "%30s %10s %10s %10s\n" ("index"::String) ("o-F"::String) ("o-M"::String) ("o-T"::String)
  mapM_ (\(k,v) -> printf "%30s %10.2f %10.2f %10.2f\n" (show k) v (omt ! k) (ott ! k)) $ assocs oft
  printf "%10.8f\n" sc
  printf "%30s %10s %10s %10s %6s %6s\n" ("index"::String) ("i-M"::String) ("o-M"::String) ("i*o / sc"::String) ("lbl 1" :: String) ("lbl 2" :: String)
  mapM_ (\(k,k1,k2) -> let k' = unsafeCoerce k
                       in  printf "%30s %10.7f %10.7f %10.7f %6s %6s\n" (show k) (imt ! k) (omt ! k') ((imt!k) * (omt!k') / sc) (maybe "-" label $ F.label t1 VG.!? k1) (maybe "-" label $ F.label t2 VG.!? k2)
        ) [ (Z:.TreeIxR frst1 k1 T:.TreeIxR frst2 k2 T,k1,k2) | k1 <- [lb1 .. ub1], k2 <- [lb2 .. ub2] ]


main :: IO ()
main = return ()

