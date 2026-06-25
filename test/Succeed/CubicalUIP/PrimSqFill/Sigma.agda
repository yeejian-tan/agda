{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.Sigma where

open import CubicalUIP.Prim
open import Agda.Builtin.Sigma

module _ (A : Type) (B : A → Type) where
  sigmaPrim : SqFill (Σ A (λ a → B a))
  sigmaPrim = sqFill (Σ A (λ a → B a))

  sigmaManual : SqFill (Σ A (λ a → B a))
  sigmaManual = SqFillSigma A (sqFill A) B λ a → sqFill (B a)

  checkSigma : (λ {lu} {ld} → sigmaPrim {lu} {ld}) ≡ sigmaManual
  checkSigma i = sigmaPrim
