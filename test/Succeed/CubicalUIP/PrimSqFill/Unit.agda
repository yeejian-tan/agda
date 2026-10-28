{-# OPTIONS --cubical=uip #-}

-- ⊤ has no builtin SqFill proof: it is an empty record with eta, whose squares are constant
-- (see Record.agda).

module CubicalUIP.PrimSqFill.Unit where

open import CubicalUIP.Prim
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
  using (Term; TC; bindTC; normalise; unify; typeError; strErr; termErr; con)

-- ⊤ has eta, so any two squares are equal: check the normal form instead.
macro
  reducesToCon : Term → Term → TC ⊤
  reducesToCon t hole = bindTC (normalise t) λ where
    (con _ _) → unify hole (con (quote tt) [])
    t'         → typeError (strErr "did not reduce to a constructor:" ∷ termErr t' ∷ [])

module _ {x₀₀ x₀₁ x₁₀ x₁₁ : ⊤}
         (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁) (i j : I) where

  check : ⊤
  check = reducesToCon (sqFill ⊤ l r u d i j)
