{-# OPTIONS --cubical=uip #-}

-- List has no builtin SqFill proof: it is a data type like any other (see Data.agda). Squares
-- with constructor-headed edges are pushed into the arguments, constant squares are constant.

module CubicalUIP.PrimSqFill.List where

open import CubicalUIP.Prim
open import Agda.Builtin.List
open import Agda.Builtin.Nat

module _ {ℓ} (A : Type ℓ) {x₀₀ x₀₁ x₁₀ x₁₁ : A}
       (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁) (xs : List A) where

  -- List has no eta, so these only hold if the square reduced
  pushed : sqFill (List A) (cong (λ a → a ∷ a ∷ []) l) (cong (λ a → a ∷ a ∷ []) r)
                           (cong (λ a → a ∷ a ∷ []) u) (cong (λ a → a ∷ a ∷ []) d)
         ≡ (λ i j → let a = sqFill A l r u d i j in a ∷ a ∷ [])
  pushed = refl

  -- the tail xs is the same on all edges: its square is constant
  neutralTail : sqFill (List A) (cong (_∷ xs) l) (cong (_∷ xs) r) (cong (_∷ xs) u) (cong (_∷ xs) d)
              ≡ (λ i j → sqFill A l r u d i j ∷ xs)
  neutralTail = refl

  constant : sqFill (List A) {xs} {xs} refl {xs} {xs} refl refl refl ≡ refl
  constant _ _ _ = xs

-- Closed constant squares do not traverse the list.
module Long where

  upTo : Nat → List Nat
  upTo zero    = []
  upTo (suc n) = n ∷ upTo n

  xs : List Nat
  xs = upTo 5000

  check : sqFill (List Nat) {xs} {xs} refl {xs} {xs} refl refl refl ≡ refl
  check _ _ _ = xs
