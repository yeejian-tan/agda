{-# OPTIONS --cubical=uip #-}

-- Bool has no builtin SqFill proof: it is a data type like any other (see Data.agda). Its
-- constructors have no arguments, so constructor-headed edges are constant.

module CubicalUIP.PrimSqFill.Bool where

open import CubicalUIP.Prim
open import Agda.Builtin.Bool

-- Bool has no eta, so these only hold if the square reduced
checkTrue : sqFill Bool {true} {true} refl {true} {true} refl refl refl ≡ refl
checkTrue _ _ _ = true

checkFalse : sqFill Bool {false} {false} refl {false} {false} refl refl refl ≡ refl
checkFalse _ _ _ = false

checkNeutral : (b : Bool) → sqFill Bool {b} {b} refl {b} {b} refl refl refl ≡ refl
checkNeutral b _ _ _ = b

-- Neutral edges stay stuck, which must not break anything.
module Stuck {x₀₀ x₀₁ x₁₀ x₁₁ : Bool} (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁) where

  sq = sqFill Bool l r u d
