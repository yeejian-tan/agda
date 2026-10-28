{-# OPTIONS --cubical=uip #-}

-- Maybe has no builtin SqFill proof: it is a data type like any other (see Data.agda).

module CubicalUIP.PrimSqFill.Maybe where

open import CubicalUIP.Prim
open import Agda.Builtin.Maybe

module _ {ℓ} (A : Type ℓ) {x₀₀ x₀₁ x₁₀ x₁₁ : A}
       (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁) where

  -- Maybe has no eta, so these only hold if the square reduced
  pushed : sqFill (Maybe A) (cong just l) (cong just r) (cong just u) (cong just d)
         ≡ (λ i j → just (sqFill A l r u d i j))
  pushed = refl

  constant : sqFill (Maybe A) {nothing} {nothing} refl {nothing} {nothing} refl refl refl ≡ refl
  constant _ _ _ = nothing
