{- |
Module      : KanExtension
Описание    : Расширения Кана вдоль профункторов на конечных носителях,
              обогащённые категории (hom со значениями в квантали),
              Йонеда-пополнение и двойственность Исбелла.

Полностью полиморфен по Quantale q: над UnitInterval это теория Пытьева,
над Bool — классическая логика предикатов (Pl = exists, Bel = forall).

-- ИДЕИ РАСШИРЕНИЯ:
--  * Носители-домены вместо списков: class Finite a / непрерывные X с sup по компактам.
--  * Прообразные/образные профункторы общего вида и композиция профункторов
--    (coend по среднему аргументу) — категория Prof как библиотечный объект.
--  * Взвешенные (ко)пределы как обобщение lanAlong/ranAlong.
--  * Isbell envelope как отдельный тип (неподвижные точки Spec . O) и
--    tight span для метрик Ловера.
-}
module KanExtension where

import Quantale

-- | Профунктор E -|-> A со значениями в квантали q.
type Prof q a e = e -> a -> q

-- | Левое расширение Кана (coend): Lan(tau)(e) = joins_x [ prof e x (x) tau x ].
lanAlong :: Quantale q => Prof q a e -> [a] -> (a -> q) -> e -> q
lanAlong prof xs tau e = joins [ qTensor (prof e x) (tau x) | x <- xs ]

-- | Правое расширение Кана (end): Ran(tb)(e) = meets_x [ prof e x -o tb x ].
ranAlong :: Quantale q => Prof q a e -> [a] -> (a -> q) -> e -> q
ranAlong prof xs tb e = meets [ qHom (prof e x) (tb x) | x <- xs ]

-- | Профунктор принадлежности [x in E].
memberProf :: (Eq a, Quantale q) => Prof q a [a]
memberProf e x = if x `elem` e then qUnit else lbot

-- | Профунктор дополнения [x notin E] = theta_{0,1} от memberProf.
complementProf :: (Eq a, Quantale q) => Prof q a [a]
complementProf e x = if x `elem` e then lbot else qUnit

-- | Pl(E) = Lan вдоль принадлежности = sup_{x in E} tau(x).
plMeasure :: (Eq a, Quantale q) => [a] -> (a -> q) -> [a] -> q
plMeasure dom tau = lanAlong memberProf dom tau

-- | Bel(E) = Ran вдоль дополнения = inf_{x notin E} tauBar(x).
belMeasure :: (Eq a, Quantale q) => [a] -> (a -> q) -> [a] -> q
belMeasure dom tauBar = ranAlong complementProf dom tauBar

-- ============================================================
-- Обогащённые категории: hom со значениями в q
-- ============================================================

-- | hom-матрица q-обогащённой категории (для Пытьева: степень неразличимости).
type EnrichedHom q a = a -> a -> q

-- | tensor-транзитивность: hom(x,y) (x) hom(y,z) <= hom(x,z).
isTransitive :: Quantale q => EnrichedHom q a -> [a] -> Bool
isTransitive hom xs = and
  [ qTensor (hom x y) (hom y z) <= hom x z
  | x <- xs, y <- xs, z <- xs ]

-- | Условие преснопа: hom(x,y) (x) phi(y) <= phi(x).
isPresheaf :: Quantale q => EnrichedHom q a -> [a] -> (a -> q) -> Bool
isPresheaf hom xs phi = and
  [ qTensor (hom x y) (phi y) <= phi x | x <- xs, y <- xs ]

-- | Йонеда-пополнение (Lan вдоль вложения Йонеды): наименьший пресноп >= tau.
yonedaHat :: Quantale q => EnrichedHom q a -> [a] -> (a -> q) -> a -> q
yonedaHat hom xs tau x = joins [ qTensor (hom x y) (tau y) | y <- xs ]

-- ============================================================
-- Двойственность Исбелла: O -| Spec
-- ============================================================

-- | O(phi)(c) = meets_x [ phi(x) -o hom(x,c) ].
isbellO :: Quantale q => EnrichedHom q a -> [a] -> (a -> q) -> a -> q
isbellO hom xs phi c = meets [ qHom (phi x) (hom x c) | x <- xs ]

-- | Spec(psi)(c) = meets_x [ psi(x) -o hom(c,x) ].
isbellSpec :: Quantale q => EnrichedHom q a -> [a] -> (a -> q) -> a -> q
isbellSpec hom xs psi c = meets [ qHom (psi x) (hom c x) | x <- xs ]

-- | Единица сопряжения: phi <= Spec(O(phi)).
checkIsbellUnit :: Quantale q => EnrichedHom q a -> [a] -> (a -> q) -> Bool
checkIsbellUnit hom xs phi =
  and [ phi x <= isbellSpec hom xs (isbellO hom xs phi) x | x <- xs ]

-- | Треугольное тождество: O . Spec . O = O.
checkIsbellTriangle :: Quantale q => EnrichedHom q a -> [a] -> (a -> q) -> Bool
checkIsbellTriangle hom xs phi =
  and [ o1 x =~ o2 x | x <- xs ]
  where
    o1 = isbellO hom xs phi
    o2 = isbellO hom xs (isbellSpec hom xs o1)
