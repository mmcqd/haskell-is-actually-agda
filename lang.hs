{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE PolyKinds  #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

import Data.Kind
import GHC.Types (Symbol)
import Data.Void

infix 2 ==
data (==) :: k -> k -> Type where
  Refl :: a == a

type Not a = a -> Void

infixr 5 :->
data Ty :: Type where
  Nat   :: Ty
  (:->) :: Ty -> Ty -> Ty

data Term :: Type where
  Var :: Symbol -> Term
  App :: Term -> Term -> Term
  Lam :: Symbol -> Ty -> Term -> Term
  Z   :: Term
  S   :: Term -> Term 


data Context :: Type where
  E :: Context
  C :: Symbol -> Ty -> Context -> Context

data Lookup :: Context -> Symbol -> Ty -> Type where
  ZZ :: Lookup (C x t g) x t 
  SS :: Not (x == y) -> Lookup g x t -> Lookup (C y t' g) x t

data (|-) :: Context -> (Term,Ty) -> Type where
  
  VarT :: Lookup g x t -> 
          g |- '(Var x, t)

  AppT :: g |- '(m, a :-> b) -> 
          g |- '(n, a) ->
          g |- '(App m n, b)

  LamT :: (C x a g) |- '(n,b) ->
          g |- '(Lam x a n, a :-> b) 

  ZT   :: g |- '(Z, Nat)

  ST   :: g |- '(n, Nat) ->
          g |- '(S n, Nat)

d :: E |- '(S Z, Nat)
d = ST ZT

d' ::  g |- 
  '(Lam "x" (Nat :-> Nat) (Lam "y" Nat (App (Var "x") (Var "y"))), (Nat :-> Nat) :-> Nat :-> Nat)
d' = LamT (LamT (AppT (VarT (SS (\(Refl) -> undefined) ZZ)) (VarT ZZ))) 



