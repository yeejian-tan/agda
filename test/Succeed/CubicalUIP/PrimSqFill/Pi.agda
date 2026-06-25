{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.Pi where

open import CubicalUIP.Prim

module _ (A : Type) (B : A → Type) where
  piPrim : SqFill ((a : A) → B a)
  piPrim = sqFill ((a : A) → B a)

  piManual : SqFill ((a : A) → B a)
  piManual = SqFillPi A (λ a → B a) (λ a → sqFill (B a))

  checkPi : (λ {lu} {ld} → piPrim {lu} {ld}) ≡ piManual
  checkPi _ = piPrim
