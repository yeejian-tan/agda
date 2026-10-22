{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.Record where

open import CubicalUIP.Prim

module Eta {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') where

  record R : Type (ℓ ⊔ ℓ') where
    field
      a : A
      b : B a
      c : B a → A
  open R

  module _ {x₀₀ x₀₁ x₁₀ x₁₁ : R}
           (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁) where

    sq = sqFill R l r u d

    -- the record square is computed fieldwise
    checkA : (λ i j → sq i j .a) ≡ sqFill A (cong a l) (cong a r) (cong a u) (cong a d)
    checkA = refl

    -- with eta, the boundary holds definitionally
    checkL : (λ j → sq i0 j) ≡ l
    checkL = refl

    checkD : (λ i → sq i i1) ≡ d
    checkD = refl

module NoEta (A : Type) where

  record R : Type where
    no-eta-equality
    field
      a : A
      c : A → A
  open R

  module _ {x₀₀ x₀₁ x₁₀ x₁₁ : R}
           (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁) where

    sq = sqFill R l r u d

    -- without eta, the square only computes when projected
    checkA : (λ i j → sq i j .a) ≡ sqFill A (cong a l) (cong a r) (cong a u) (cong a d)
    checkA = refl
