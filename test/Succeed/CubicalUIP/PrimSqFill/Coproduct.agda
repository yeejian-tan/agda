{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.Coproduct where

open import CubicalUIP.Prim
open import Agda.Builtin.Coproduct

module _ (A : Type) where
  coproductPrim : SqFill (A ⊎ A)
  coproductPrim = sqFill (A ⊎ A)

  coproductManual : SqFill (A ⊎ A)
  coproductManual = SqFillCoproduct A (sqFill A) A (sqFill A)

  checkCoproduct : (λ {lu} {ld} → coproductPrim {lu} {ld}) ≡ coproductManual
  checkCoproduct i {lu} {ld} = coproductPrim {lu} {ld}
