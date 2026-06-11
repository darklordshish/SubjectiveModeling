{- |
Пример 1: ТЕОРИЯ ВОЗМОЖНОСТЕЙ.

Одна монада распределений @Dist r@ — три теории, в зависимости от полукольца:

  * @UnitInterval@ (max, min)  — возможностная динамика (sup-min цепи);
  * @ProbW@        (+, *)      — марковская цепь;
  * @Bool@         (||, &&)    — достижимость.

Плюс нечёткая логика как квантале [0,1]: t-норма min = qTensor,
импликация Гёделя = residuation qHom.
-}
module Main where

import Quantale
import Distribution
import qualified Data.Map.Strict as M

-- Погода: одно и то же пространство состояний для всех трёх теорий.
data W = Sun | Rain | Fog deriving (Show, Eq, Ord)

-- | Возможностное переходное ядро: "из Sun вполне возможно остаться в Sun,
--   туман возможен на 0.4, дождь маловероятен (0.2)". Нормировка: sup = 1.
stepPoss :: W -> Poss W
stepPoss Sun  = possOf [(Sun, 1.0), (Fog, 0.4), (Rain, 0.2)]
stepPoss Rain = possOf [(Rain, 1.0), (Fog, 0.7), (Sun, 0.3)]
stepPoss Fog  = possOf [(Fog, 1.0), (Sun, 0.6), (Rain, 0.6)]

-- | Вероятностное ядро той же структуры: нормировка sum = 1.
stepProb :: W -> Dist ProbW W
stepProb Sun  = distOf [(Sun, ProbW 0.7), (Fog, ProbW 0.2), (Rain, ProbW 0.1)]
stepProb Rain = distOf [(Rain, ProbW 0.5), (Fog, ProbW 0.3), (Sun, ProbW 0.2)]
stepProb Fog  = distOf [(Fog, ProbW 0.4), (Sun, ProbW 0.3), (Rain, ProbW 0.3)]

-- | Булево ядро: просто граф переходов (какие переходы вообще есть).
stepBool :: W -> Dist Bool W
stepBool Sun  = distOf [(Sun, True), (Fog, True)]
stepBool Rain = distOf [(Rain, True)]
stepBool Fog  = distOf [(Fog, True), (Rain, True)]

-- Нечёткие предикаты (классика Заде).
tall :: Int -> Double
tall h
  | h < 160   = 0.0
  | h > 190   = 1.0
  | otherwise = fromIntegral (h - 160) / 30.0

young :: Int -> Double
young a
  | a < 20    = 1.0
  | a > 50    = 0.0
  | otherwise = fromIntegral (50 - a) / 30.0

main :: IO ()
main = do
  putStrLn "=== Possibility theory on the shared categorical core ==="
  putStrLn ""
  putStrLn "-- One bindD, three theories (same state space W):"
  mapM_ (\n -> putStrLn ("  [Poss]  step " ++ show n ++ ": "
         ++ showDistList (nStepsD n stepPoss Sun))) [1, 2, 3]
  putStrLn ("  [Poss]  stabilises at step 2: "
            ++ show (eqDist (nStepsD 2 stepPoss Sun) (nStepsD 3 stepPoss Sun)))
  putStrLn ""
  mapM_ (\n -> putStrLn ("  [Prob]  step " ++ show n ++ ": "
         ++ showDistList (nStepsD n stepProb Sun))) [1, 2]
  let mass d = sum [ x | ProbW x <- M.elems (runDist d) ]
  putStrLn ("  [Prob]  total mass after 3 steps: "
            ++ show (mass (nStepsD 3 stepProb Sun)))
  putStrLn ""
  mapM_ (\n -> putStrLn ("  [Bool]  reachable in " ++ show n ++ " steps: "
         ++ showDistList (nStepsD n stepBool Sun))) [1, 2]
  putStrLn ""
  putStrLn "-- Monad laws hold over every semiring (checked numerically):"
  let m0 = possOf [(Sun, 1.0), (Rain, 0.5)]
      kP w = possOf [(w, 1.0), (Fog, 0.5)]
  putStrLn ("  [Poss]  " ++ show (checkMonadLaws m0 stepPoss kP Sun))
  let etaP w = distOf [(w, ProbW 1)]
  putStrLn ("  [Prob]  " ++ show (checkMonadLaws (etaP Sun) stepProb etaP Sun))
  let etaB w = distOf [(w, True)]
  putStrLn ("  [Bool]  " ++ show (checkMonadLaws (etaB Sun) stepBool etaB Sun))
  putStrLn ""
  putStrLn "-- Fuzzy logic = the quantale [0,1] itself:"
  putStrLn ("  tall(175) AND young(30) (t-norm min = qTensor): "
            ++ show (unUI (qTensor (ui (tall 175)) (ui (young 30)))))
  putStrLn ("  Goedel implication 0.8 -> 0.6 (residuation qHom): "
            ++ show (unUI (qHom (ui 0.8) (ui 0.6))))
  putStrLn ("  residuation adjunction on the grid: "
            ++ show (checkResiduationAdj gammaGrid))
