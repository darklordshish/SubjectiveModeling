{- |
Пример 2: СУБЪЕКТИВНОЕ МОДЕЛИРОВАНИЕ ПЫТЬЕВА.

Сюжет: диагностика двигателя. Эксперт задаёт распределение правдоподобий
неисправностей; библиотека считает меры Pl/Bel (как расширения Кана),
кондиционирует по наблюдению через residuation, комбинирует двух экспертов,
оценивает энтропии и строит оптимальное правило идентификации; в финале —
неразличимость состояний как обогащённый hom и tight span Исбелла.
-}
module Main where

import Quantale
import KanExtension
import SubjectiveModel

-- Возможные состояния двигателя.
data Fault = EngineOK | Misfire | Overheat | PumpFail
  deriving (Show, Eq, Ord, Enum, Bounded)

faults :: [Fault]
faults = [minBound .. maxBound]

-- | Эксперт 1: "скорее всего всё в порядке, перебои зажигания вполне
--   правдоподобны, перегрев сомнителен, отказ насоса почти исключён".
tauExpert1 :: Fault -> Double
tauExpert1 EngineOK = 1.0
tauExpert1 Misfire  = 0.7
tauExpert1 Overheat = 0.4
tauExpert1 PumpFail = 0.1

-- | Дуально согласованная модель: tauBar = theta . tau (Пытьев, Замеч. 1.1).
model1 :: SubjModel Fault
model1 = dualConsistent faults tauExpert1

-- Наблюдение: температура.
data Temp = TNormal | THigh deriving (Show, Eq, Ord)

-- | Возможность наблюдения при данной неисправности, g(o; x).
likelihood :: Fault -> Temp -> Double
likelihood EngineOK TNormal = 1.0
likelihood EngineOK THigh   = 0.2
likelihood Misfire  TNormal = 1.0
likelihood Misfire  THigh   = 0.4
likelihood Overheat TNormal = 0.3
likelihood Overheat THigh   = 1.0
likelihood PumpFail TNormal = 0.4
likelihood PumpFail THigh   = 1.0

-- | Совместное распределение (Pl-независимая склейка, Опр. 1.2): min.
tauJoint :: (Fault, Temp) -> Double
tauJoint (f, o) = min (tauExpert1 f) (likelihood f o)

jointDom :: [(Fault, Temp)]
jointDom = [ (f, o) | f <- faults, o <- [TNormal, THigh] ]

main :: IO ()
main = do
  putStrLn "=== Pytyev subjective modeling: engine diagnostics ==="
  putStrLn ""
  putStrLn "-- Expert 1 plausibilities (dually consistent model):"
  mapM_ (\f -> putStrLn ("  tau(" ++ show f ++ ") = " ++ show (tauExpert1 f))) faults
  let serious = [Overheat, PumpFail]
  putStrLn ""
  putStrLn "-- Measures (Pl = Lan along membership, Bel = Ran along complement):"
  putStrLn ("  Pl(serious)  = " ++ show (smPl model1 serious))
  putStrLn ("  Bel(serious) = " ++ show (smBel model1 serious))
  putStrLn ("  Pl(not serious)  = " ++ show (smPl model1 [EngineOK, Misfire]))
  putStrLn ("  Bel(not serious) = " ++ show (smBel model1 [EngineOK, Misfire]))
  putStrLn ""
  putStrLn "-- Conditioning on THigh (residuation, no subjective rescaling):"
  mapM_ (\f -> putStrLn ("  tau(" ++ show f ++ " | THigh) = "
         ++ show (condTau jointDom tauJoint THigh f))) faults
  putStrLn "   (normalised automatically: sup over faults is 1)"
  putStrLn ""
  putStrLn "-- Combining expert 1 with empirical ranking (pairwise matrices):"
  let empirical = [0.5, 0.9, 0.8, 0.2]   -- данные намекают на Misfire/Overheat
      ranks = combineDistributions (map tauExpert1 faults) empirical 0.5 0.5
  putStrLn ("  ranks = " ++ show ranks)
  putStrLn ("  order = " ++ show (rankOrder faults ranks))
  putStrLn ""
  putStrLn "-- Entropies of the subjective model:"
  putStrLn ("  informativity = " ++ show (subjInformativity model1))
  putStrLn ("  uncertainty   = " ++ show (subjUncertainty model1))
  putStrLn ""
  putStrLn "-- Optimal identification rule (loss-possibility minimax):"
  let obs k z = if k == z then 1.0 else 0.3 :: Double
      loss k d = if k == d then 0.0 else 0.8 :: Double
  mapM_ (\(z, d) -> putStrLn ("  d*(" ++ show z ++ ") = " ++ show d))
        (optimalDecision [1, 2] [1, 2] obs loss)
  putStrLn ""
  putStrLn "-- Indistinguishability of faults as an enriched hom; Isbell:"
  let homF :: Fault -> Fault -> UnitInterval
      homF x y | x == y = ltop
      homF Overheat PumpFail = ui 0.6   -- симптомы похожи
      homF PumpFail Overheat = ui 0.6
      homF _ _ = ui 0.2
      tauQ = ui . tauExpert1
      tauHat = yonedaHat homF faults tauQ
  putStrLn ("  raw tau is a presheaf: " ++ show (isPresheaf homF faults tauQ))
  putStrLn ("  Yoneda completion: "
            ++ show [ (f, unUI (tauHat f)) | f <- faults ])
  putStrLn ("  Isbell unit + triangle: "
            ++ show (checkIsbellUnit homF faults tauHat
                     && checkIsbellTriangle homF faults tauHat))
  let tight = isbellSpec homF faults (isbellO homF faults tauHat)
  putStrLn ("  tight span: " ++ show [ (f, unUI (tight f)) | f <- faults ])
