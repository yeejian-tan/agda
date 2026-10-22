{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.Maybe where

open import CubicalUIP.Prim
open import Agda.Builtin.Maybe

module _ (A : Type) where
  maybePrim : SqFill (Maybe A)
  maybePrim = sqFill (Maybe A)

  maybeManual : SqFill (Maybe A)
  maybeManual = SqFillMaybe A (sqFill A)

  checkMaybe : (λ {lu} {ld} → maybePrim {lu} {ld}) ≡ maybeManual
  checkMaybe i {lu} {ld} = maybePrim {lu} {ld}
