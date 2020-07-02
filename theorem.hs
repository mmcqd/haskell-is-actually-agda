
{-# LANGUAGE DataKinds,
             GADTs,
             TypeOperators,
             PolyKinds,
             KindSignatures,
             TypeFamilies
#-}

import Data.Kind

infix 5 ==
data (==) :: k -> k -> Type where
  Refl :: a == a

sym :: a == b -> b == a
sym Refl = Refl

trans :: a == b -> b == c -> a == c
trans Refl Refl = Refl

(<=>) = trans

cong :: a == b -> f a == f b
cong Refl = Refl

data Nat :: Type where
  Z :: Nat
  S :: Nat -> Nat

data SNat :: Nat -> Type where
  ZZ :: SNat Z
  SS :: SNat n -> SNat (S n)

type family (+) (a :: Nat) (b :: Nat) where
  Z     + b = b
  (S a) + b = S (a + b)


plus_assoc :: SNat m -> SNat n -> SNat p -> m + (n + p) == (m + n) + p
plus_assoc ZZ     n p = Refl
plus_assoc (SS m) n p = cong $ plus_assoc m n p

plus_id_r :: SNat m -> m + Z == m
plus_id_r ZZ     = Refl
plus_id_r (SS m) = cong $ plus_id_r m

plus_suc :: SNat m -> SNat n -> m + S n == S (m + n)
plus_suc ZZ     n = Refl
plus_suc (SS m) n = cong $ plus_suc m n

plus_comm :: SNat m -> SNat n -> m + n == n + m
plus_comm m ZZ     = plus_id_r m
plus_comm m (SS n) = plus_suc m n <=> (cong $ plus_comm m n)


data (<=) :: Nat -> Nat -> Type where
  ZlteN :: Z <= n
  SlteS :: n <= m -> S n <= S m

inv_SlteS :: S m <= S n -> m <= n
inv_SlteS (SlteS p) = p

inv_ZlteN :: m <= Z -> m == Z
inv_ZlteN ZlteN = Refl

lte_refl :: SNat n -> n <= n
lte_refl ZZ     = ZlteN
lte_refl (SS n) = SlteS (lte_refl n)

lte_trans :: m <= n -> n <= p -> m <= p
lte_trans ZlteN      _          = ZlteN
lte_trans (SlteS mn) (SlteS np) = SlteS $ lte_trans mn np

