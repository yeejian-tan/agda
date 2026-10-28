{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.Integration where

open import CubicalUIP.Prim
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Builtin.Product

-- Structural: the reduct of the primitive is the composition of the builtin SqFill*.
-- Every type former appears: Pi, Σ (dependent), × (non-dependent Σ), ≡ (non-dependent PathP),
-- PathP, records, a neutral family B, and the types without a builtin proof (⊤, Bool, Nat, List,
-- Maybe, ⊎; see Data.agda and Unit.agda), which stay as sqFill.
module Structural (A : Type) (a : A) (B : Bool → Type) {x y : Bool} (q : x ≡ y) (b₀ : B x) (b₁ : B y) where

  record R : Type where
    field
      r₁ : A
      r₂ : Bool

  F : Bool × Maybe (List A) → Type
  F p = (B (fst p) ⊎ R) × (a ≡ a)

  P : Type
  P = PathP (λ i → B (q i)) b₀ b₁

  Body : Type
  Body = Σ (Bool × Maybe (List A)) F × P × (Nat × ⊤)

  Ty : Type
  Ty = (n : Nat) → Body

  prim : SqFill Ty
  prim = sqFill Ty

  manual : SqFill Ty
  manual = SqFillPi Nat (λ _ → Body) λ _ →
    SqFillProduct (Σ (Bool × Maybe (List A)) F)
      (SqFillSigma (Bool × Maybe (List A))
        (SqFillProduct Bool (sqFill Bool) (Maybe (List A)) (sqFill (Maybe (List A))))
        F λ p →
        SqFillProduct (B (fst p) ⊎ R)
          (sqFill (B (fst p) ⊎ R))
          (a ≡ a) (SqFillPath A a a (sqFill A)))
      (P × (Nat × ⊤))
      (SqFillProduct P (SqFillPathP (B x) (B y) b₀ b₁ (λ i → B (q i)) (sqFill (B x)))
        (Nat × ⊤) (SqFillProduct Nat (sqFill Nat) ⊤ (sqFill ⊤)))

  check : (λ {lu} {ld} → prim {lu} {ld}) ≡ manual
  check k = prim

-- Computational: on a closed type, filling a constant square computes to the constant.
module Computational where

  record R : Type where
    field
      r₁ : Nat
      r₂ : Maybe Bool

  Ty : Type
  Ty = (⊤ → ⊤) → Σ Bool (λ { true → ⊤ ; false → (Nat × List R) ⊎ Bool })

  tm : Ty
  tm _ = false , inl (3 , record { r₁ = 1 ; r₂ = just true } ∷ [])

  sq = sqFill Ty {tm} {tm} refl {tm} {tm} refl refl refl

  check : sq ≡ refl
  check _ _ _ = tm
