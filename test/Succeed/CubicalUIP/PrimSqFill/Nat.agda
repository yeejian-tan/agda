{-# OPTIONS --cubical=uip #-}

-- Nat has no builtin SqFill proof: it is a data type like any other (see Data.agda).
-- Literals count as constructor-headed.

module CubicalUIP.PrimSqFill.Nat where

open import CubicalUIP.Prim
open import Agda.Builtin.Nat

module _ {x₀₀ x₀₁ x₁₀ x₁₁ : Nat}
       (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁) (n : Nat) where

  -- Nat has no eta, so these only hold if the square reduced
  pushed : sqFill Nat (cong (λ m → suc (suc m)) l) (cong (λ m → suc (suc m)) r)
                      (cong (λ m → suc (suc m)) u) (cong (λ m → suc (suc m)) d)
         ≡ (λ i j → suc (suc (sqFill Nat l r u d i j)))
  pushed = refl

  constant : sqFill Nat {n} {n} refl {n} {n} refl refl refl ≡ refl
  constant _ _ _ = n

-- Edges that are literals and edges headed by suc agree on the constructor.
module Literal (p : 3 ≡ 3) where

  check : sqFill Nat (cong suc p) (cong suc p) (λ _ → 4) (λ _ → 4)
        ≡ (λ i j → suc (sqFill Nat p p refl refl i j))
  check = refl

-- Closed constant squares do not count down the literal.
module Large where

  check : sqFill Nat {1000000} {1000000} refl {1000000} {1000000} refl refl refl ≡ refl
  check _ _ _ = 1000000
