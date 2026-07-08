-- | Тесты законов библиотеки. Без внешних зависимостей: только base/containers.
--   Каждая проверка — численная верификация категорного закона на конечных данных.
module Main where

import Quantale
import KanExtension
import Bitopos
import Distribution
import SubjectiveModel

import Control.Monad (filterM)
import Data.List ((\\))
import System.Exit (exitFailure, exitSuccess)
import qualified Data.Map.Strict as M

check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn ((if ok then "[OK]   " else "[FAIL] ") ++ name)
  return ok

main :: IO ()
main = do
  let grid5 = map ui [0, 0.25, 0.5, 0.75, 1]

  -- Данные для Kan-тестов
  let dom = "abcd"
      tauD 'a' = 1.0
      tauD 'b' = 0.6
      tauD 'c' = 0.4
      tauD 'd' = 0.1
      tauD _   = 0.0
      tauBarD = (1 -) . tauD
      subsets = filterM (const [True, False]) dom
      pl e  = unUI (plMeasure dom (ui . tauD) e)
      bel e = unUI (belMeasure dom (ui . tauBarD) e)
      plDirect e  = maximum (0 : map tauD e)
      belDirect e = minimum (1 : map tauBarD (dom \\ e))

  -- Обогащённый hom для Йонеды/Исбелла
  let pts = "xyz" :: String
      homE :: Char -> Char -> UnitInterval
      homE a b | a == b = ltop
      homE 'x' 'y' = ui 0.7
      homE 'y' 'x' = ui 0.7
      homE _ _ = ui 0.5
      tauRaw = ui . (\c -> case c of { 'x' -> 1.0; 'y' -> 0.2; _ -> 0.1 })
      tauHat = yonedaHat homE pts tauRaw
      spec1 = isbellSpec homE pts (isbellO homE pts tauHat)
      spec2 = isbellSpec homE pts (isbellO homE pts spec1)

  -- Ядра для монадных законов
  let stepPoss :: Char -> Poss Char
      stepPoss 'x' = possOf [('x', 1.0), ('y', 0.4)]
      stepPoss 'y' = possOf [('y', 1.0), ('z', 0.7)]
      stepPoss _   = possOf [('z', 1.0), ('x', 0.6)]
      kPoss c = possOf [(c, 1.0), ('y', 0.5)]
      m0 = possOf [('x', 1.0), ('z', 0.5)]
      stepProb :: Char -> Dist ProbW Char
      stepProb 'x' = distOf [('x', ProbW 0.7), ('y', ProbW 0.3)]
      stepProb 'y' = distOf [('y', ProbW 0.6), ('z', ProbW 0.4)]
      stepProb _   = distOf [('z', ProbW 0.5), ('x', ProbW 0.5)]
      etaP c = distOf [(c, ProbW 1)]
      stepBool :: Char -> Dist Bool Char
      stepBool 'x' = distOf [('x', True), ('y', True)]
      stepBool 'y' = distOf [('y', True)]
      stepBool _   = distOf [('z', True), ('x', True)]
      etaB c = distOf [(c, True)]
      probMass d = sum [ x | ProbW x <- M.elems (runDist d) ]

  -- Кондиционирование
  let jdom = [ (z1, z2) | z1 <- [1, 2 :: Int], z2 <- [1, 2 :: Int] ]
      tauJ :: (Int, Int) -> Double
      tauJ (1, 1) = 1.0
      tauJ (2, 1) = 0.6
      tauJ (1, 2) = 0.4
      tauJ (2, 2) = 0.4
      tauJ _      = 0.0
      marg = margZ2 jdom tauJ
      cnd z1 z2 = condTau jdom tauJ z2 z1
      gridD = map (\k -> fromIntegral k / 20) [0 .. 20 :: Int]

  -- Слой Пытьева
  let smE = dualConsistent [1, 2, 3 :: Int]
              (\x -> case x of { 1 -> 1.0; 2 -> 0.7; _ -> 0.3 })
      obs k z = if k == z then 1.0 else 0.3 :: Double
      loss k d = if k == d then 0.0 else 0.8 :: Double

  results <- sequence
    [ -- Quantale
      check "UnitInterval: residuation adjunction (11^3 triples)"
        (checkResiduationAdj gammaGrid)
    , check "UnitInterval: frame distributivity over subsets"
        (checkFrameDistributivity grid5)
    , check "Bool: residuation adjunction"
        (checkResiduationAdj [False, True])
    , check "Bool: frame distributivity"
        (checkFrameDistributivity [False, True])
    , check "theta is a dual isomorphism (max <-> min)"
        (isDualIso theta)
    , check "theta is NOT a quantale automorphism"
        (not (isQuantaleAuto theta))
    , check "t^2 and sqrt are quantale automorphisms"
        (isQuantaleAuto gammaSq && isQuantaleAuto gammaSqrt)
      -- Kan extensions
    , check "Pl = Lan along membership = direct sup (16 subsets)"
        (all (\e -> ui (pl e) =~ ui (plDirect e)) subsets)
    , check "Bel = Ran along complement = direct inf (16 subsets)"
        (all (\e -> ui (bel e) =~ ui (belDirect e)) subsets)
    , check "dual consistency: Bel(E) = theta (Pl (X \\ E))"
        (all (\e -> ui (bel e) =~ theta (ui (pl (dom \\ e)))) subsets)
    , check "[Bool] Pl degenerates to exists, Bel to forall"
        (plMeasure [1, 2, 3 :: Int] (> 1) [2, 3]
         && not (belMeasure [1, 2, 3 :: Int] (> 1) [2, 3]))
    , check "imageModel is functorial: Pl/Bel transform by preimage (incl. phi = id)"
        (let m = SubjModel dom tauD tauBarD
             phi c = if c `elem` "ab" then 'u' else 'v'
             mY  = imageModel m phi "uv"
             mId = imageModel m id dom
             pre a = [ x | x <- dom, phi x `elem` a ]
             subsY = filterM (const [True, False]) "uv"
         in all (\a -> ui (smPl mY a) =~ ui (smPl m (pre a))
                    && ui (smBel mY a) =~ ui (smBel m (pre a))) subsY
            && all (\e -> ui (smBel mId e) =~ ui (smBel m e)
                       && ui (smPl mId e) =~ ui (smPl m e)) subsets)
      -- Yoneda / Isbell
    , check "hom is tensor-transitive"
        (isTransitive homE pts)
    , check "raw tau is not a presheaf, Yoneda completion is"
        (not (isPresheaf homE pts tauRaw) && isPresheaf homE pts tauHat)
    , check "Yoneda completion dominates tau and is idempotent"
        (all (\x -> tauRaw x <= tauHat x) pts
         && all (\x -> yonedaHat homE pts tauHat x =~ tauHat x) pts)
    , check "Isbell unit: phi <= Spec (O phi)"
        (checkIsbellUnit homE pts tauHat)
    , check "Isbell triangle: O Spec O = O"
        (checkIsbellTriangle homE pts tauHat)
    , check "Spec . O is idempotent"
        (all (\x -> spec1 x =~ spec2 x) pts)
      -- Distribution monad
    , check "[Poss] monad laws"
        (checkMonadLaws m0 stepPoss kPoss 'x')
    , check "[ProbW] monad laws"
        (checkMonadLaws (etaP 'x') stepProb etaP 'x')
    , check "[Bool] monad laws"
        (checkMonadLaws (etaB 'x') stepBool etaB 'x')
    , check "[Poss] normalisation preserved (sup = 1 after bind)"
        (ui (supPoss (bindD m0 stepPoss)) =~ ltop)
    , check "[ProbW] mass preserved (sum = 1 after 3 steps)"
        (ProbW (probMass (nStepsD 3 stepProb 'x')) =~ ProbW 1)
    , check "[Poss] sup-min powers stabilise"
        (eqDist (nStepsD 3 stepPoss 'x') (nStepsD 4 stepPoss 'x'))
      -- Conditioning = residuation
    , check "conditioning solves Pytyev's equation"
        (and [ ui (min (cnd z1 z2) (marg z2)) =~ ui (tauJ (z1, z2))
             | z1 <- [1, 2], z2 <- [1, 2] ])
    , check "conditioning is the LARGEST solution (grid)"
        (and [ c <= cnd z1 z2 + 1e-9
             | z1 <- [1, 2], z2 <- [1, 2], c <- gridD
             , ui (min c (marg z2)) =~ ui (tauJ (z1, z2)) ])
    , check "conditional distribution is normalised (sup = 1)"
        (and [ ui (maximum [ cnd z1 z2 | z1 <- [1, 2] ]) =~ ltop
             | z2 <- [1, 2] ])
      -- Pytyev layer
    , check "entropies on the canonical example (0.3 / 0.7)"
        (ui (subjInformativity smE) =~ ui 0.3
         && ui (subjUncertainty smE) =~ ui 0.7)
    , check "absolute ignorance: informativity 0, uncertainty 1"
        (ui (subjInformativity (absoluteIgnorance [1, 2, 3 :: Int])) =~ ui 0
         && ui (subjUncertainty (absoluteIgnorance [1, 2, 3 :: Int])) =~ ui 1)
    , check "optimal identification rule is the diagonal"
        (optimalDecision [1, 2] [1, 2] obs loss == [(1, 1), (2, 2)])
    , check "expert combination ranks (identical orders agree)"
        (combineDistributions [1.0, 0.8, 0.5, 0.2] [0.9, 0.7, 0.6, 0.3] 0.5 0.5
         == [3, 2, 1, 0])
      -- Bilattice
    , check "interval bilattice: lattice laws for <=t and <=k"
        (checkLatticeLaws leqT joinT meetT && checkLatticeLaws leqK joinK meetK)
    , check "interval bilattice: interlacing"
        checkInterlacing
    , check "joinK(unknown, true) = true (knowledge refinement)"
        (joinK bUnknown bTrue == bTrue)
    ]

  let failed = length (filter not results)
  putStrLn ""
  putStrLn (show (length results) ++ " checks, " ++ show failed ++ " failed")
  if failed == 0 then exitSuccess else exitFailure
