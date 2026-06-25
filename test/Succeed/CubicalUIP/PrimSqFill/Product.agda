{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.Product where

open import CubicalUIP.Prim
open import Agda.Builtin.Product

module _ (A : Type) where
  productPrim : SqFill (A × A)
  productPrim =  sqFill (A × A)

  productManual : SqFill (A × A)
  productManual = SqFillProduct A (sqFill A) A (sqFill A)

  checkProduct : (λ {lu} {ld} → productPrim {lu} {ld}) ≡ productManual
  checkProduct i = productPrim
