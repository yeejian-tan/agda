{-# OPTIONS --cubical=uip #-}

-- Shared prelude for the prim^sqFill regression tests in CubicalUIP/PrimSqFill/: the tests
-- check what the primitive reduces to, e.g. the builtin SqFill* proofs of
-- Agda.Builtin.Cubical.SqFill, which declares the primitives and binds the builtins.

module CubicalUIP.Prim where

open import CubicalUIP.Helper public
open import Agda.Builtin.Cubical.SqFill public

sqFill : ∀{ℓ} (A : Type ℓ) → SqFill A
sqFill = prim^sqFill

infixr 1 _⊎_

data _⊎_ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
