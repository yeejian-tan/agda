{-# OPTIONS --cubical=uip #-}

-- ⊎ has no builtin SqFill proof: it is a data type like any other (see Data.agda).

module CubicalUIP.PrimSqFill.Coproduct where

open import CubicalUIP.Prim

module _ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') {x₀₀ x₀₁ x₁₀ x₁₁ : A}
       (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁) where

  -- ⊎ has no eta, so these only hold if the square reduced
  pushedInl : sqFill (A ⊎ B) (cong inl l) (cong inl r) (cong inl u) (cong inl d)
            ≡ (λ i j → inl (sqFill A l r u d i j))
  pushedInl = refl

  pushedInr : sqFill (B ⊎ A) (cong inr l) (cong inr r) (cong inr u) (cong inr d)
            ≡ (λ i j → inr (sqFill A l r u d i j))
  pushedInr = refl
