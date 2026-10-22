{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.List where

open import CubicalUIP.Prim
open import Agda.Builtin.List

module _ (A : Type) where
  listPrim : SqFill (List A)
  listPrim = sqFill (List A)

  listManual : SqFill (List A)
  listManual = SqFillList A (sqFill A)

  checkList : (λ {lu} {ld} → listPrim {lu} {ld}) ≡ listManual
  checkList i {lu} {ld} = listPrim {lu} {ld}
