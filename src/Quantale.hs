{- |
Module      : Quantale
Описание    : Ядро категорной библиотеки — решётки, квантали, [0,1], инволюция theta, группа Gamma.

Полиморфный слой: Lattice / Quantale с инстансами UnitInterval и Bool.
Слой, специфичный для [0,1] (theta, Gamma), — внизу модуля.

-- ИДЕИ РАСШИРЕНИЯ:
--  * Квантале Лукасевича на [0,1]: qTensor a b = max 0 (a+b-1), qHom a b = min 1 (1-a+b)
--    (newtype Luka = Luka Double) — даст нечёткую логику Лукасевича из S4 Uncertainty.
--  * Тропическое квантале ([0,inf], +, 0) с обратным порядком — метрики Ловера буквально.
--  * Некоммутативные квантали (qTensor /= flip qTensor): два residuation-а qHomL/qHomR.
--  * Инволюция как параметр: class Quantale q => InvolutiveQuantale q where inv :: q -> q
--    (для произвольной theta из класса Theta Пытьева, не только 1-t).
--  * Полные решётки с Sup по произвольным семействам (сейчас joins/meets только по спискам).
-}
module Quantale where

import Data.List (subsequences)

-- | Приближённое равенство (для Double-подобных носителей).
class ApproxEq q where
  (=~) :: q -> q -> Bool
infix 4 =~

-- | Ограниченная решётка с порядком из Ord.
class (Ord q, ApproxEq q) => Lattice q where
  ljoin :: q -> q -> q
  lmeet :: q -> q -> q
  lbot  :: q
  ltop  :: q

joins :: Lattice q => [q] -> q
joins = foldr ljoin lbot

meets :: Lattice q => [q] -> q
meets = foldr lmeet ltop

-- | Коммутативное единичное квантале: моноидальная sup-решётка с residuation.
--   Закон сопряжения: qTensor a c <= b  <=>  c <= qHom a b
class Lattice q => Quantale q where
  qTensor :: q -> q -> q
  qUnit   :: q
  qHom    :: q -> q -> q

-- ============================================================
-- Инстанс 1: [0,1] с tensor = min (фрейм; основная шкала Пытьева)
-- ============================================================

newtype UnitInterval = UI Double deriving (Eq, Ord, Show)

-- | Конструктор с обрезкой в [0,1].
ui :: Double -> UnitInterval
ui = UI . max 0 . min 1

unUI :: UnitInterval -> Double
unUI (UI x) = x

instance ApproxEq UnitInterval where
  UI a =~ UI b = abs (a - b) < 1e-9

instance Lattice UnitInterval where
  ljoin (UI a) (UI b) = UI (max a b)
  lmeet (UI a) (UI b) = UI (min a b)
  lbot = UI 0
  ltop = UI 1

instance Quantale UnitInterval where
  qTensor = lmeet
  qUnit   = ltop
  qHom (UI a) (UI b) = if a <= b then UI 1 else UI b

-- ============================================================
-- Инстанс 2: Bool — классическая логика (Pl = exists, Bel = forall)
-- ============================================================

instance ApproxEq Bool where
  (=~) = (==)

instance Lattice Bool where
  ljoin = (||)
  lmeet = (&&)
  lbot = False
  ltop = True

instance Quantale Bool where
  qTensor = (&&)
  qUnit   = True
  qHom a b = not a || b   -- импликация

-- ============================================================
-- Полиморфные проверки законов (по переданной сетке значений)
-- ============================================================

-- | Сопряжение residuation: min(a,c) <= b  <=>  c <= a -o b.
checkResiduationAdj :: Quantale q => [q] -> Bool
checkResiduationAdj grid = and
  [ (qTensor a c <= b) == (c <= qHom a b)
  | a <- grid, b <- grid, c <- grid ]

-- | Дистрибутивность tensor над joins (свойство фрейма/квантале).
--   На подмножествах сетки (сетку передавать небольшую).
checkFrameDistributivity :: Quantale q => [q] -> Bool
checkFrameDistributivity grid = and
  [ qTensor a (joins s) =~ joins (map (qTensor a) s)
  | a <- grid, s <- subsequences grid ]

-- ============================================================
-- Слой [0,1]: инволюция theta и группа автоморфизмов Gamma
-- ============================================================

-- | Дуальный изоморфизм theta(t) = 1 - t: переводит (max,min) в (min,max).
theta :: UnitInterval -> UnitInterval
theta (UI t) = UI (1 - t)

-- | Стандартная сетка для численных проверок.
gammaGrid :: [UnitInterval]
gammaGrid = [ UI (fromIntegral k / 10) | k <- [0 .. 10 :: Int] ]

gammaSq, gammaSqrt :: UnitInterval -> UnitInterval
gammaSq   (UI t) = UI (t * t)
gammaSqrt (UI t) = UI (sqrt t)

-- | gamma - автоморфизм квантали ([0,1], max, min)?
isQuantaleAuto :: (UnitInterval -> UnitInterval) -> Bool
isQuantaleAuto g = and
  [ g (ljoin a b) =~ ljoin (g a) (g b) &&
    g (lmeet a b) =~ lmeet (g a) (g b)
  | a <- gammaGrid, b <- gammaGrid ]
  && g lbot =~ lbot && g ltop =~ ltop

-- | theta - дуальный изоморфизм (max <-> min)?
isDualIso :: (UnitInterval -> UnitInterval) -> Bool
isDualIso f = and
  [ f (ljoin a b) =~ lmeet (f a) (f b) &&
    f (lmeet a b) =~ ljoin (f a) (f b)
  | a <- gammaGrid, b <- gammaGrid ]
