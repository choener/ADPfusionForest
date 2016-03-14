
module Main where

import           Control.Monad(forM_)
import           Data.List (nub)
import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Data.Tree as T
import qualified Data.Vector as V
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Generic as VG

import           ADP.Fusion
import           Biobase.Newick
import           Data.Forest.Static (TreeOrder(..),Forest)
import           Data.PrimitiveArray as PA hiding (map)
import           FormalLanguage.CFG
import qualified Data.Forest.Static as F

import           Data.Forest.Static.AlignRL
import           Data.Forest.Static.Node



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
[P,F] -> done    <<< [e,e]
[F,P] -> done    <<< [e,e]
[F,P] -> fpalign <<< [T,T] [F,P]
[F,P] -> fpdelin <<< [T,Y] [F,P]
[F,P] -> fpindel <<< [Z,T] [G,P]
[G,F] -> gfalign <<< [T,T] [G,F]
[G,F] -> gfdelin <<< [T,Z] [P,G]
[G,F] -> gfindel <<< [Y,T] [G,F]
[G,F] -> done    <<< [e,e]
[F,G] -> done    <<< [e,e]
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

Emit: Global
|]

makeAlgebraProduct ''SigGlobal

score :: Monad m => Int -> Int -> Int -> SigGlobal m Int Int Info Info
score m a d = SigGlobal -- Match Affine Deletion costs 
  { done  = \ (Z:.():.()) -> 0
  , iter  = \ t f -> tSI glb ("TFTFTFTFTF",t,f) $ t+f
  , align = \ (Z:.c:.b) f -> tSI glb ("ALIGN",f,c,b) $ f + if label c == label b then m else - 100
  , indel = \ (Z:.():.b) f -> tSI glb ("INDEL",f,b) $ f - d --gap open
  , delin = \ (Z:.c:.()) f -> tSI glb ("DELIN",f,c) $ f - d --gap open
  , afdelin = \ (Z:.c:.()) f -> tSI glb ("AFDELIN",f,c) $ f - a --gap extension
  , afindel = \ (Z:.():.b) f -> tSI glb ("AFINDEL",f,b) $ f - a --gap extension
  , fpalign = \ t f -> t + f
  , pfalign = \ t f -> t + f
  , gpalign = \ t f -> t + f
  , pgalign = \ t f -> t + f
  , gfalign = \ t f -> t + f
  , fgalign = \ t f -> t + f
  , fpdelin = \ t f -> t + f
  , pfdelin = \ t f -> t + f
  , pgdelin = \ t f -> t + f
  , gpdelin = \ t f -> t + f
  , fgdelin = \ t f -> t + f
  , gfdelin = \ t f -> t + f
  , fpindel = \ t f -> t + f
  , pfindel = \ t f -> t + f
  , fgindel = \ t f -> t + f
  , gfindel = \ t f -> t + f
  , pgindel = \ t f -> t + f
  , gpindel = \ t f -> t + f
  , h     = SM.foldl' max (-88888)
  }
{-# Inline score #-}


type Pretty' = [[T.Tree (Info,Info)]]
pretty' :: Monad m => SigGlobal m [T.Tree (Info,Info)] [[T.Tree ((Info,Info))]] Info Info
pretty' = SigGlobal
  { done  = \ (Z:.():.()) -> []
  , iter  = \ t f -> t++f
  , align = \ (Z:.a:.b) f -> [T.Node (a,b) f]
  , indel = \ (Z:.():.b) f -> [T.Node (Info "-" 0,b) f]
  , delin = \ (Z:.a:.()) f -> [T.Node (a,Info "-" 0) f]
  , afdelin = \ (Z:.a:.()) f -> [T.Node (a,Info "." 0) f]
  , afindel = \ (Z:.():.b) f -> [T.Node (Info "." 0,b) f]
  , fpalign = \ t f -> t ++ f
  , pfalign = \ t f -> t ++ f
  , gpalign = \ t f -> t ++ f
  , pgalign = \ t f -> t ++ f
  , gfalign = \ t f -> t ++ f
  , fgalign = \ t f -> t ++ f
  , fpdelin = \ t f -> t ++ f
  , pfdelin = \ t f -> t ++ f
  , pgdelin = \ t f -> t ++ f
  , gpdelin = \ t f -> t ++ f
  , fgdelin = \ t f -> t ++ f
  , gfdelin = \ t f -> t ++ f
  , fpindel = \ t f -> t ++ f
  , pfindel = \ t f -> t ++ f
  , fgindel = \ t f -> t ++ f
  , gfindel = \ t f -> t ++ f
  , pgindel = \ t f -> t ++ f
  , gpindel = \ t f -> t ++ f
  , h     = SM.toList
  }
{-# Inline pretty' #-}



type Trix = TreeIxR Pre V.Vector Info I
type Tbl x = ITbl Id Unboxed (Z:.EmptyOk:.EmptyOk) (Z:.Trix:.Trix) x
type Frst = Forest Pre V.Vector Info

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
                           (node $ F.label f1)
                           (node $ F.label f2)



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
                    (node $ F.label f1) (node $ F.label f2)


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


main :: IO ()
main = return ()

