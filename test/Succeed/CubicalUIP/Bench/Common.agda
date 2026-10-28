{-# OPTIONS --cubical=uip #-}

module CubicalUIP.Bench.Common where

open import CubicalUIP.Prim public
open import Agda.Builtin.List public
open import Agda.Builtin.Maybe public
open import Agda.Builtin.Nat public renaming (Nat to ℕ)
open import Agda.Builtin.Bool public
open import Agda.Builtin.Unit public
open import Agda.Builtin.Coproduct public

data ListD {ℓ} (A : Type ℓ) : Type ℓ where
  nilD : ListD A
  _∷D_ : A → ListD A → ListD A

data MaybeD {ℓ} (A : Type ℓ) : Type ℓ where
  nothingD : MaybeD A
  justD : A → MaybeD A

data NatD : Type where
  zeroD : NatD
  sucD : NatD → NatD

data BoolD : Type where
  trueD falseD : BoolD

record UnitD : Type where
  constructor ttD

data _⊎D_ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
  inlD : A → A ⊎D B
  inrD : B → A ⊎D B

-- the square under a function f, in the expected form
Nice : ∀ {ℓ ℓ'} (A : Type ℓ) {B : Type ℓ'} (f : A → B) → SqFill B → Type (ℓ ⊔ ℓ')
Nice A f s = ∀ {x₀₀ x₀₁ x₁₀ x₁₁ : A} (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁)
  → s (cong f l) (cong f r) (cong f u) (cong f d) ≡ (λ i j → f (sqFill A l r u d i j))
