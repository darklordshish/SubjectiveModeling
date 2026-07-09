{- |
Module      : SubjectiveModel
Описание    : Слой теории Пытьева поверх Quantale/KanExtension.
              API в Double для читаемости ноутбуков; внутри делегирует
              полиморфному ядру через UnitInterval.

-- ИДЕИ РАСШИРЕНИЯ:
--  * [СДЕЛАНО] SubjModelQ над произвольной кванталью (полиморфный слой ниже);
--    второй вариант (зарубки Scale + проекторы projUp/projDown/clampScale);
--    третий вариант (Goguen) и Лукасевич — через Quantale.hs. См. PytevIso §9.
--  * Условные распределения как настоящее Kleisli-стрелы монады возможности.
--  * Эмпирическое восстановление (п. 2.1.2): тип Observation y + g^eta как Prof.
-}
module SubjectiveModel where

import Quantale
import KanExtension
import Data.List (sortBy)
import Data.Ord (comparing)

-- | Субъективная модель НОЭ: домен + распределения правдоподобий и доверий.
data SubjModel a = SubjModel
  { smDomain :: [a]
  , smTau    :: a -> Double   -- tau(x)    = Pl(x~ = x)
  , smTauBar :: a -> Double   -- tauBar(x) = Bel(x~ = x)
  }

-- ============================================================
-- Конструкторы
-- ============================================================

absoluteIgnorance :: [a] -> SubjModel a
absoluteIgnorance xs = SubjModel xs (const 1.0) (const 0.0)

exactKnowledge :: Eq a => [a] -> a -> SubjModel a
exactKnowledge xs x0 = SubjModel xs ind ind
  where ind x = if x == x0 then 1.0 else 0.0

-- | Дуально согласованная модель: tauBar = theta . tau.
dualConsistent :: [a] -> (a -> Double) -> SubjModel a
dualConsistent xs tau = SubjModel xs tau (unUI . theta . ui . tau)

isDuallyConsistent :: SubjModel a -> Bool
isDuallyConsistent m = all chk (smDomain m)
  where chk x = ui (smTauBar m x) =~ theta (ui (smTau m x))

-- ============================================================
-- Меры Pl и Bel — через расширения Кана из ядра
-- ============================================================

smPl :: Eq a => SubjModel a -> [a] -> Double
smPl m e = unUI (plMeasure (smDomain m) (ui . smTau m) e)

smBel :: Eq a => SubjModel a -> [a] -> Double
smBel m e = unUI (belMeasure (smDomain m) (ui . smTauBar m) e)

-- | Образ НОЭ под phi : X -> Y — функториальный пушфорвард:
--   tau'    = Lan_phi tau    (sup по слою),
--   tauBar' = Ran_phi tauBar (inf по слою; ко-синглетонное распределение).
--   Тогда Pl_Y = Pl_X . preimage и Bel_Y = Bel_X . preimage (естественность
--   формул образов; доказательство и контрпример к «событийному» прочтению
--   п. 1.4 — ноутбук PytevIso.ipynb курса, теорема 2 / проверка C7).
imageModel :: Eq b => SubjModel a -> (a -> b) -> [b] -> SubjModel b
imageModel m phi ys = SubjModel ys tau' tauBar'
  where
    xs = smDomain m
    tau'    y = maximum (0 : [smTau m x    | x <- xs, phi x == y])
    tauBar' y = minimum (1 : [smTauBar m x | x <- xs, phi x == y])

-- | «Событийное» прочтение п. 1.4 Пытьева: Bel(y~ = y) = Bel_X(phi^{-1}{y}) =
--   inf_{phi(x) /= y} tauBar(x). Это доверие к СОБЫТИЮ «y~ = y», а не компонент
--   распределения: подстановка его в inf_{y notin A} не восстанавливает Bel_Y
--   уже при phi = id (Bel определяется на ко-синглетонах, а не на синглетонах).
eventBelAt :: Eq b => SubjModel a -> (a -> b) -> b -> Double
eventBelAt m phi y = minimum (1 : [smTauBar m x | x <- smDomain m, phi x /= y])

-- | Действие автоморфизма gamma из Gamma на модель.
applyGamma :: (Double -> Double) -> SubjModel a -> SubjModel a
applyGamma g m = m { smTau = g . smTau m }

-- ============================================================
-- Полиморфный слой: субъективная модель над произвольной кванталью
--   (варианты теории = смена шкалы; см. PytevIso.ipynb, раздел 9).
--   Параллелен Double-фасаду выше: старый API не ломается.
-- ============================================================

-- | Субъективная модель со шкалой значений в квантали q.
data SubjModelQ q a = SubjModelQ
  { smqDomain :: [a]
  , smqTau    :: a -> q   -- Pl-плотность
  , smqTauBar :: a -> q   -- Bel-плотность (ко-синглетонная)
  }

-- | Дуально согласованная модель: tauBar = inv . tau. Требует инволютивной
--   квантали — для Гогена (max,*) НЕ компилируется (самодуальной инволюции нет).
dualConsistentQ :: InvolutiveQuantale q => [a] -> (a -> q) -> SubjModelQ q a
dualConsistentQ xs tau = SubjModelQ xs tau (inv . tau)

-- | Pl(E) = sup_{x in E} tau(x) — через расширение Кана из ядра (любая кванталь).
smqPl :: (Eq a, Quantale q) => SubjModelQ q a -> [a] -> q
smqPl m = plMeasure (smqDomain m) (smqTau m)

-- | Bel(E) = inf_{x notin E} tauBar(x) — Ran вдоль дополнения.
smqBel :: (Eq a, Quantale q) => SubjModelQ q a -> [a] -> q
smqBel m = belMeasure (smqDomain m) (smqTauBar m)

-- | Функториальный пушфорвард под phi: tau' = Lan_phi (sup по слою),
--   tauBar' = Ran_phi (inf по слою). Pl_Y = Pl_X . preimage для любой квантали.
imageModelQ :: (Eq b, Quantale q) => SubjModelQ q a -> (a -> b) -> [b] -> SubjModelQ q b
imageModelQ m phi ys = SubjModelQ ys tau' tauBar'
  where
    xs = smqDomain m
    tau'    y = joins [ smqTau m x    | x <- xs, phi x == y ]
    tauBar' y = meets [ smqTauBar m x | x <- xs, phi x == y ]

-- | Маргинал по второй координате (кванталь-версия).
margQ :: (Eq b, Quantale q) => [(a, b)] -> ((a, b) -> q) -> b -> q
margQ dom tauJ z2 = joins [ tauJ (a, b) | (a, b) <- dom, b == z2 ]

-- | Условное распределение = residuation tau(z2) -o tauJ(z1,z2): наибольшее
--   решение уравнения tau(z2) (x) c = tauJ(z1,z2). Форма зависит от варианта:
--   усечение (Гёдель), деление (Гоген), min(1,1-a+b) (Лукасевич).
condTauQ :: (Eq b, Quantale q) => [(a, b)] -> ((a, b) -> q) -> b -> a -> q
condTauQ dom tauJ z2 z1 = qHom (margQ dom tauJ z2) (tauJ (z1, z2))

-- ============================================================
-- Вариант-2: содержательные «зарубки» шкалы (неподвижные точки) и проекторы
-- ============================================================

-- | Зарубки — упорядоченный набор неподвижных точек шкалы (кроме 0 и 1).
type Scale q = [q]

-- | Проектор (u)⌣_a = a \/ u — «сдвиг снизу»: заменяет значения ниже a на a.
projUp :: Quantale q => q -> q -> q
projUp = ljoin

-- | Проектор (u)⌢_a = a (x) u — «скалярное действие»: у Гёделя min(a,u).
projDown :: Quantale q => q -> q -> q
projDown = qTensor

-- | Зажим значения в неподвижный интервал [lo,hi] = (u ⌣_lo) ⌢_hi.
--   Для идемпотентной шкалы (Гёдель) — обычный clamp min(hi, max(lo,u)).
clampScale :: Quantale q => q -> q -> q -> q
clampScale lo hi u = projDown hi (projUp lo u)

-- ============================================================
-- Интегралы (Теорема 1.1) — bind монады возможности в развёрнутом виде
-- ============================================================

plIntegral :: [a] -> (a -> Double) -> (a -> Double) -> Double
plIntegral xs tau g = maximum (0 : [min (tau x) (g x) | x <- xs])

belIntegral :: [a] -> (a -> Double) -> (a -> Double) -> Double
belIntegral xs tauBar gBar = minimum (1 : [max (tauBar x) (gBar x) | x <- xs])

-- ============================================================
-- Независимость (Определение 1.2)
-- ============================================================

plJointDist :: SubjModel a -> SubjModel b -> (a, b) -> Double
plJointDist m1 m2 (a, b) = min (smTau m1 a) (smTau m2 b)

belJointDist :: SubjModel a -> SubjModel b -> (a, b) -> Double
belJointDist m1 m2 (a, b) = max (smTauBar m1 a) (smTauBar m2 b)

-- ============================================================
-- Кондиционирование = residuation (правый сопряжённый к min(-, tau(z2)))
-- ============================================================

-- | Маргинал по второй координате.
margZ2 :: Eq b => [(a, b)] -> ((a, b) -> Double) -> b -> Double
margZ2 dom tauJ z2 = maximum (0 : [tauJ (a, b) | (a, b) <- dom, b == z2])

-- | Условное распределение tau(z1|z2) = tau(z2) -o tauJ(z1,z2):
--   максимальное решение уравнения min(c, tau(z2)) = tauJ(z1,z2),
--   нормированное (sup по z1 равен 1) без субъективной шкалы gamma_z2.
condTau :: Eq b => [(a, b)] -> ((a, b) -> Double) -> b -> a -> Double
condTau dom tauJ z2 z1 =
  unUI (qHom (ui (margZ2 dom tauJ z2)) (ui (tauJ (z1, z2))))

-- ============================================================
-- Энтропии (Часть 2, разд. 2)
-- ============================================================

subjInformativity :: SubjModel a -> Double
subjInformativity m = plIntegral (smDomain m) (smTau m) (smTauBar m)

subjUncertainty :: SubjModel a -> Double
subjUncertainty m = belIntegral (smDomain m) (smTauBar m) (smTau m)

dualEntropy :: SubjModel a -> Double
dualEntropy m = plIntegral (smDomain m) (smTau m) ((1 -) . smTau m)

thirdVariantEntropy :: SubjModel a -> Double
thirdVariantEntropy m = maximum
  (0 : [ t * logBase 2 (1 / t) | x <- smDomain m, let t = smTau m x, t > 0 ])

-- ============================================================
-- Идентификация состояний (Часть 2, разд. 3)
-- ============================================================

-- | Оптимальное правило: d*(z) = argmin_d max_k min(loss k d, obs k z).
optimalDecision :: [Int] -> [Int] -> (Int -> Int -> Double) -> (Int -> Int -> Double)
                -> [(Int, Int)]
optimalDecision zSpace kSpace obs loss = [ (z, optD z) | z <- zSpace ]
  where
    optD z = foldr1 (\a b -> if cost z a <= cost z b then a else b) kSpace
    cost z d = maximum [ min (loss k d) (obs k z) | k <- kSpace ]

-- ============================================================
-- Комбинирование субъективного и эмпирического (п. 2.2)
-- ============================================================

compMatrix :: [Double] -> [[Int]]
compMatrix vals = [ [ cmp vi vj | vj <- vals ] | vi <- vals ]
  where
    cmp a b
      | a > b     = 1
      | a < b     = -1
      | otherwise = 0

matrixDist :: [[Int]] -> [[Int]] -> Double
matrixDist m1 m2 = sqrt . fromIntegral $ sum
  [ (m1 !! i !! j - m2 !! i !! j) ^ (2 :: Int)
  | i <- [0 .. length m1 - 1], j <- [0 .. length (head m1) - 1] ]

-- | Ранги оптимального совместного распределения по средневзвешенной матрице.
combineDistributions :: [Double] -> [Double] -> Double -> Double -> [Double]
combineDistributions subj empi w0 w1 =
  let mS = compMatrix subj
      mE = compMatrix empi
      n  = length subj
      mBar i j = w0 * fromIntegral (mS !! i !! j) + w1 * fromIntegral (mE !! i !! j)
      rank i = fromIntegral (length [ j | j <- [0 .. n - 1], mBar i j > 0 ])
  in [ rank i | i <- [0 .. n - 1] ]

-- | Сортировка элементов по убыванию ранга (утилита для демо).
rankOrder :: [a] -> [Double] -> [a]
rankOrder xs rs = map snd (sortBy (comparing (negate . fst)) (zip rs xs))
