{- |
Module      : Distribution
Описание    : Общая монада распределений над коммутативным полукольцом.
              Специализации: возможность (UnitInterval: max/min),
              дискретная вероятность (ProbW: +/*), достижимость (Bool: ||/&&).

bind = "интеграл" по полукольцу: для UnitInterval это в точности pl-интеграл
Пытьева (Теорема 1.1), для ProbW — формула полной вероятности.

-- ИДЕИ РАСШИРЕНИЯ:
--  * Полукольцо Виттерби (max, *) — наиболее правдоподобные траектории HMM.
--  * Тропическое (min, +) — кратчайшие пути; bindD станет алгоритмом Беллмана-Форда.
--  * Лог-полукольцо (logsumexp, +) — численно устойчивые вероятности.
--  * Weighted automata: nStepsD над свободным полукольцом регулярных выражений.
--  * Связь с Giry: непрерывный носитель через интеграл вместо Map (см. S3 Uncertainty).
--  * instance Quantale q => Semiring q (после включения FlexibleInstances/overlap).
-}
module Distribution where

import Quantale
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

-- | Коммутативное полукольцо.
class Semiring r where
  szero  :: r
  sone   :: r
  splus  :: r -> r -> r
  stimes :: r -> r -> r

-- | Возможность: (max, min) на [0,1].
instance Semiring UnitInterval where
  szero  = lbot
  sone   = ltop
  splus  = ljoin
  stimes = lmeet

-- | Дискретный вероятностный вес: (+, *).
newtype ProbW = ProbW Double deriving (Eq, Ord, Show)

instance Semiring ProbW where
  szero = ProbW 0
  sone  = ProbW 1
  splus  (ProbW a) (ProbW b) = ProbW (a + b)
  stimes (ProbW a) (ProbW b) = ProbW (a * b)

instance ApproxEq ProbW where
  ProbW a =~ ProbW b = abs (a - b) < 1e-9

-- | Достижимость: (||, &&).
instance Semiring Bool where
  szero  = False
  sone   = True
  splus  = (||)
  stimes = (&&)

-- ============================================================
-- Монада распределений
-- ============================================================

newtype Dist r a = Dist { runDist :: Map a r } deriving (Show)

distOf :: (Semiring r, Ord a) => [(a, r)] -> Dist r a
distOf = Dist . M.fromListWith splus

-- | eta: дельта Дирака = "точное знание" Пытьева.
diracD :: (Semiring r, Ord a) => a -> Dist r a
diracD x = distOf [(x, sone)]

-- | bind: свёртка по полукольцу (pl-интеграл / полная вероятность).
bindD :: (Semiring r, Ord b) => Dist r a -> (a -> Dist r b) -> Dist r b
bindD (Dist m) k = distOf
  [ (b, stimes ra rb) | (a, ra) <- M.toList m, (b, rb) <- M.toList (runDist (k a)) ]

-- | Композиция ядер Клейсли.
kleisliD :: (Semiring r, Ord c) => (a -> Dist r b) -> (b -> Dist r c) -> a -> Dist r c
kleisliD f g a = bindD (f a) g

-- | n шагов переходного ядра.
nStepsD :: (Semiring r, Ord a) => Int -> (a -> Dist r a) -> a -> Dist r a
nStepsD 0 _ x = diracD x
nStepsD n k x = bindD (nStepsD (n - 1) k x) k

-- | Сравнение распределений с допуском (нулевые веса игнорируются).
eqDist :: (Ord a, Semiring r, ApproxEq r) => Dist r a -> Dist r a -> Bool
eqDist (Dist m1) (Dist m2) =
  M.keysSet f1 == M.keysSet f2 && and (M.elems (M.intersectionWith (=~) f1 f2))
  where
    f1 = M.filter (not . (=~ szero)) m1
    f2 = M.filter (not . (=~ szero)) m2

-- | Законы монады на конкретных данных (left id, right id, assoc).
checkMonadLaws :: (Semiring r, ApproxEq r, Ord a)
               => Dist r a -> (a -> Dist r a) -> (a -> Dist r a) -> a -> Bool
checkMonadLaws m k1 k2 x0 =
  eqDist (bindD (diracD x0) k1) (k1 x0)
  && eqDist (bindD m diracD) m
  && eqDist (bindD (bindD m k1) k2) (bindD m (\x -> bindD (k1 x) k2))

-- ============================================================
-- Специализация: возможность
-- ============================================================

type Poss a = Dist UnitInterval a

possOf :: Ord a => [(a, Double)] -> Poss a
possOf = distOf . map (\(a, t) -> (a, ui t))

-- | sup распределения (1.0 = нормировано по Пытьеву).
supPoss :: Poss a -> Double
supPoss (Dist m) = maximum (0 : map unUI (M.elems m))

showDistList :: (Show a, Show r) => Dist r a -> String
showDistList = show . M.toList . runDist
