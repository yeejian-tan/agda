{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.Path where

open import CubicalUIP.Prim

module _ (A : Type) where
  postulate
    a : A

  pathPrim : SqFill (a ≡ a)
  pathPrim = sqFill (a ≡ a)

  pathManual : SqFill (a ≡ a)
  pathManual = SqFillPath A a a (sqFill A)

  checkPath : (λ {lu} {ld} → pathPrim {lu} {ld}) ≡ pathManual
  checkPath i {lu} {ld} = pathPrim {lu} {ld}
