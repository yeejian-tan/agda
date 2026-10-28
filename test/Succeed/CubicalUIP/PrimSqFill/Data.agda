{-# OPTIONS --cubical=uip #-}

-- prim^sqFill on (non-indexed, non-higher) data types without a SqFill builtin.

module CubicalUIP.PrimSqFill.Data where

open import CubicalUIP.Prim
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

data Tree {ℓ} (A : Type ℓ) : Type ℓ where
  leaf : Tree A
  node : Tree A → A → Tree A → Tree A

if_then_else_ : Bool → Type → Type → Type
if true  then x else _ = x
if false then _ else y = y

-- the type of the second argument depends on the first
data Dep : Type where
  mk : (b : Bool) → (if b then Nat else ⊤) → Dep

-- Edges headed by the same constructor: the square is pushed into the arguments.
module Pushed {ℓ} (A : Type ℓ) {x₀₀ x₀₁ x₁₀ x₁₁ : A}
       (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁) where

  node' : A → Tree A
  node' a = node leaf a (node leaf a leaf)

  sq = sqFill (Tree A) (cong node' l) (cong node' r) (cong node' u) (cong node' d)

  -- Tree has no eta, so this only holds if the square reduced
  check : sq ≡ (λ i j → node' (sqFill A l r u d i j))
  check = refl

-- Closed squares compute to the constant.
module Closed where

  t : Tree Nat
  t = node (node leaf 1 leaf) 2 leaf

  checkTree : sqFill (Tree Nat) {t} {t} refl {t} {t} refl refl refl ≡ refl
  checkTree _ _ _ = t

  checkDep : sqFill Dep {mk true 3} {mk true 3} refl {mk true 3} {mk true 3} refl refl refl ≡ refl
  checkDep _ _ _ = mk true 3

-- Edges that are not constructor-headed stay stuck, which must not break anything.
module Stuck (A : Type) {x₀₀ x₀₁ x₁₀ x₁₁ : Tree A}
       (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁) where

  sq = sqFill (Tree A) l r u d
