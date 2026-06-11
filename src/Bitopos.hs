{- |
Module      : Bitopos
Описание    : Топологии Скотта на [0,1], индуцированная битопология на X,
              интервальный билатис [Bel, Pl].

Слой конкретен для [0,1] (Double): топологии задаются строгими неравенствами,
билатис — парами концов интервала.

-- ИДЕИ РАСШИРЕНИЯ:
--  * Топология Скотта произвольного непрерывного poset/домена (way-below relation).
--  * Битопологические пространства как объекты категории BiTop с пуями (pairwise
--    continuous maps) — и функтор из субъективных моделей в BiTop.
--  * Билатис как алгебра над произвольной решёткой L: интервалы [a,b] в L x L^op
--    (сейчас захардкожен [0,1]); связь с FOUR Белнапа как L = 2.
--  * Отрицание Гинзберга neg [a,b] = [1-b, 1-a] и его взаимодействие с theta.
-}
module Bitopos where

approxD :: Double -> Double -> Bool
approxD a b = abs (a - b) < 1e-9

-- ============================================================
-- Топологии Скотта на [0,1]
-- ============================================================

-- | Открытые T_up: (t, 1] — верхние множества по стандартному порядку.
scottUpOpen :: Double -> Double -> Bool
scottUpOpen t x = x > t

-- | Открытые T_down: [0, t) — верхние множества по обратному порядку.
scottDownOpen :: Double -> Double -> Bool
scottDownOpen t x = x < t

-- | Индуцированная tau битопология на X: открытые {x | tau x > t}.
scottUpOnX :: (a -> Double) -> Double -> [a] -> [a]
scottUpOnX tau t = filter (\x -> tau x > t)

-- | Открытые {x | tau x < t}.
scottDownOnX :: (a -> Double) -> Double -> [a] -> [a]
scottDownOnX tau t = filter (\x -> tau x < t)

-- ============================================================
-- Интервальный билатис [Bel, Pl]
-- ============================================================

data IV = IV { ivBel :: Double, ivPl :: Double } deriving (Show, Eq)

-- | Порядок истинности.
leqT :: IV -> IV -> Bool
leqT (IV a b) (IV c d) = a <= c && b <= d

-- | Порядок информации: [a,b] <=k [c,d]  <=>  [c,d] вложен в [a,b].
leqK :: IV -> IV -> Bool
leqK (IV a b) (IV c d) = a <= c && d <= b

joinT, meetT, joinK, meetK :: IV -> IV -> IV
joinT (IV a b) (IV c d) = IV (max a c) (max b d)
meetT (IV a b) (IV c d) = IV (min a c) (min b d)
joinK (IV a b) (IV c d) = IV (max a c) (min b d)  -- пересечение интервалов
meetK (IV a b) (IV c d) = IV (min a c) (max b d)  -- объединяющая оболочка

bTrue, bFalse, bUnknown, bContra :: IV
bTrue    = IV 1 1
bFalse   = IV 0 0
bUnknown = IV 0 1   -- абсолютное незнание Пытьева
bContra  = IV 1 0   -- Bel > Pl: противоречие

-- | Стандартная выборка для численных проверок законов.
ivSamples :: [IV]
ivSamples = [ IV a b | a <- [0, 0.3, 0.6, 1], b <- [0, 0.3, 0.6, 1] ]

-- | Законы решётки (поглощение/коммутативность/границы) для заданного порядка.
checkLatticeLaws :: (IV -> IV -> Bool) -> (IV -> IV -> IV) -> (IV -> IV -> IV) -> Bool
checkLatticeLaws le j m = and $
  [ le (m x y) x && le (m x y) y && le x (j x y) && le y (j x y)
  | x <- ivSamples, y <- ivSamples ] ++
  [ j x y == j y x && m x y == m y x | x <- ivSamples, y <- ivSamples ] ++
  [ j x (m x y) == x && m x (j x y) == x | x <- ivSamples, y <- ivSamples ]

-- | Interlacing: t-операции монотонны по порядку знания <=k.
checkInterlacing :: Bool
checkInterlacing = and
  [ not (leqK x y) || (leqK (joinT x z) (joinT y z) && leqK (meetT x z) (meetT y z))
  | x <- ivSamples, y <- ivSamples, z <- ivSamples ]
