{-# OPTIONS --cubical=uip #-}

-- Shared prelude for the prim^sqFill regression tests in CubicalUIP/PrimSqFill/:
-- each test checks that the primitive reduces to the corresponding builtin SqFill*.

module CubicalUIP.Prim where

open import CubicalUIP.Helper public
open import CubicalUIP.SqFillDef public
open import CubicalUIP.SqFill public

primitive
  prim^sqFill : ∀{ℓ} (A : Type ℓ) → SqFill A
  -- the data type case of prim^sqFill, which reduces to it
  prim^sqFillData : ∀{ℓ} (A : Type ℓ) → SqFill A

sqFill : ∀{ℓ} (A : Type ℓ) → SqFill A
sqFill = prim^sqFill
