{- |
Module      : Quantale
Описание    : Ядро категорной библиотеки — решётки, квантали, [0,1], инволюция theta, группа Gamma.

Полиморфный слой: Lattice / Quantale с инстансами UnitInterval и Bool.
Слой, специфичный для [0,1] (theta, Gamma), — внизу модуля.

Ссылки: квантали и residuation — Rosenthal, "Quantales and their Applications"
(1990); Goguen "L-fuzzy sets" (1967, шкала (max,*)); MV/Лукасевич — Chang (1958),
Cignoli-D'Ottaviano-Mundici (2000); theta/Gamma — Пытьев (принцип относительности
шкал). Полный разбор вариантов = квантальный спектр — PytevIso.ipynb, раздел 9.

-- ИДЕИ РАСШИРЕНИЯ:
--  * [СДЕЛАНО] Квантале Лукасевича (Luka), Гогена (Goguen), тропическое (Trop);
--    инволюция как параметр (class InvolutiveQuantale). См. PytevIso.ipynb §9.
--  * Некоммутативные квантали (qTensor /= flip qTensor): два residuation-а qHomL/qHomR.
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

-- | Квантале с дуальным изоморфизмом (инволюцией) inv : q -> q^op,
--   переводящим join <-> meet и inv . inv = id. Носитель Bel-этажа.
--   У Лукасевича inv внутренняя (inv a = a -o 0); у шкалы Гёделя [0,1]
--   inv = theta задаётся извне (residuation-отрицание вырождается в [a=0]);
--   у Гогена (max,*) самодуальной инволюции на [0,1] нет вовсе — Bel-этаж
--   уезжает в тропическую шкалу (см. dequant).
class Quantale q => InvolutiveQuantale q where
  inv :: q -> q

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
-- Инстанс 3: Гоген/Виттерби ([0,1], max, *) — психофизический вариант
--   tensor = обычное умножение; residuation = усечённое деление.
--   Свидетельства НАКАПЛИВАЮТСЯ (a * a < a): серия слабых улик топит.
-- ============================================================

newtype Goguen = Goguen Double deriving (Eq, Ord, Show)

goguen :: Double -> Goguen
goguen = Goguen . max 0 . min 1

unGoguen :: Goguen -> Double
unGoguen (Goguen x) = x

instance ApproxEq Goguen where
  Goguen a =~ Goguen b = abs (a - b) < 1e-9

instance Lattice Goguen where
  ljoin (Goguen a) (Goguen b) = Goguen (max a b)
  lmeet (Goguen a) (Goguen b) = Goguen (min a b)
  lbot = Goguen 0
  ltop = Goguen 1

instance Quantale Goguen where
  qTensor (Goguen a) (Goguen b) = Goguen (a * b)
  qUnit = Goguen 1
  qHom (Goguen a) (Goguen b) = if a <= b then Goguen 1 else Goguen (b / a)

-- ============================================================
-- Инстанс 4: Лукасевич ([0,1], max, t-норма Лукасевича) — MV-алгебра.
--   tensor a b = max(0, a+b-1) (нижняя граница Фреше для P(A и B));
--   residuation a -o b = min(1, 1-a+b); инволюция ВНУТРЕННЯЯ (1-a).
--   Предсказанный «четвёртый вариант»: шкала абсолютна (Aut = {id}),
--   состояния = вероятности (Крупа-Панти). Вишенка вероятностного моста.
-- ============================================================

newtype Luka = Luka Double deriving (Eq, Ord, Show)

luka :: Double -> Luka
luka = Luka . max 0 . min 1

unLuka :: Luka -> Double
unLuka (Luka x) = x

instance ApproxEq Luka where
  Luka a =~ Luka b = abs (a - b) < 1e-9

instance Lattice Luka where
  ljoin (Luka a) (Luka b) = Luka (max a b)
  lmeet (Luka a) (Luka b) = Luka (min a b)
  lbot = Luka 0
  ltop = Luka 1

instance Quantale Luka where
  qTensor (Luka a) (Luka b) = Luka (max 0 (a + b - 1))
  qUnit = Luka 1
  qHom (Luka a) (Luka b) = Luka (min 1 (1 - a + b))

-- ============================================================
-- Инстанс 5: тропическая шкала ([0,inf], min, +) — Bel-этаж Гогена.
--   Порядок ОБРАЩЁН (меньшее число = «правдоподобнее»): join = min,
--   meet = max, tensor = сложение, residuation = monus max(0,b-a).
--   Деквантование Маслова: Goguen <-> Trop через v = -log u.
-- ============================================================

newtype Trop = Trop Double deriving (Eq, Show)

unTrop :: Trop -> Double
unTrop (Trop x) = x

-- | Обращённый порядок: Trop a <= Trop b  <=>  a >= b (обычное).
instance Ord Trop where
  compare (Trop a) (Trop b) = compare b a

instance ApproxEq Trop where
  Trop a =~ Trop b = (isInfinite a && isInfinite b) || abs (a - b) < 1e-9

instance Lattice Trop where
  ljoin (Trop a) (Trop b) = Trop (min a b)   -- sup в обращённом порядке
  lmeet (Trop a) (Trop b) = Trop (max a b)
  lbot = Trop (1 / 0)                          -- +infinity
  ltop = Trop 0

instance Quantale Trop where
  qTensor (Trop a) (Trop b) = Trop (a + b)
  qUnit = Trop 0
  qHom (Trop a) (Trop b) = Trop (max 0 (b - a))

-- | Деквантование Маслова: Goguen (max,*) -> Trop (min,+), v = -log u.
dequant :: Goguen -> Trop
dequant (Goguen u) = Trop (if u <= 0 then 1 / 0 else negate (log u))

-- | Обратное реквантование: Trop -> Goguen, u = exp(-v).
requant :: Trop -> Goguen
requant (Trop v) = Goguen (if isInfinite v then 0 else exp (negate v))

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

-- ============================================================
-- Инволюции и полиморфные проверки над произвольной кванталью
-- ============================================================

-- | Гёдель: инволюция задаётся ИЗВНЕ (theta = 1 - t), а не через residuation.
instance InvolutiveQuantale UnitInterval where
  inv = theta

-- | Лукасевич: инволюция ВНУТРЕННЯЯ, inv a = a -o 0 = 1 - a.
instance InvolutiveQuantale Luka where
  inv a = qHom a lbot

-- | Двоично-точная сетка [0..n] значений k/n (при n = 8 — без ошибок округления).
gridFrac :: Int -> [Double]
gridFrac n = [ fromIntegral k / fromIntegral n | k <- [0 .. n] ]

-- | Автоморфизм квантали на сетке: сохраняет решётку, tensor И единицу.
--   Проверка tensor существенна — для неидемпотентных шкал (Гоген, Лукасевич)
--   решёточного автоморфизма недостаточно (монотонная a^2 сохраняет max/min,
--   но не tensor). Именно это отделяет Aut(Гоген) = {a^alpha} от Aut(решётка).
isQuantaleAutoOn :: Quantale q => [q] -> (q -> q) -> Bool
isQuantaleAutoOn grid g = and
  [ g (ljoin a b)   =~ ljoin  (g a) (g b) &&
    g (lmeet a b)   =~ lmeet  (g a) (g b) &&
    g (qTensor a b) =~ qTensor (g a) (g b)
  | a <- grid, b <- grid ]
  && g lbot =~ lbot && g ltop =~ ltop && g qUnit =~ qUnit

-- | inv - дуальный изоморфизм квантали на сетке (inv.inv = id, join <-> meet)?
isInvolution :: InvolutiveQuantale q => [q] -> Bool
isInvolution grid = and
  [ inv (inv a) =~ a &&
    inv (ljoin a b) =~ lmeet (inv a) (inv b) &&
    inv (lmeet a b) =~ ljoin (inv a) (inv b)
  | a <- grid, b <- grid ]

-- | Строгие уровни tensor-факторизуются <=> tensor идемпотентна (<=> tensor = min):
--   {a (x) b > t} = {a > t} cap {b > t}. Водораздел «уровни = морфизмы монад».
levelsFactor :: Quantale q => [q] -> Bool
levelsFactor grid = and
  [ (qTensor a b > t) == (a > t && b > t) | a <- grid, b <- grid, t <- grid ]
