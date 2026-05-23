{-# OPTIONS --cubical-compatible --safe --no-sized-types --no-guardedness --no-irrelevance --level-universe #-}

module Agda.Builtin.Product where

open import Agda.Primitive
open import Agda.Sigma

_×_ : ∀{a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

{-# BUILTIN PRODUCT _×_ #-}
