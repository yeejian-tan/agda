{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.Arr where

open import CubicalUIP.Prim

module _ (A B : Type) where
  p : SqFill (A → B)
  p = prim^sqFill (A → B)

  q = SqFillPi A (λ _ → B) (λ _ → sqFill B)

  check : (λ {lu} {ld} → p {lu} {ld}) ≡ q
  check k = p
