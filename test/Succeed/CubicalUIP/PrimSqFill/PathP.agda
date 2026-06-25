{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.PathP where

open import CubicalUIP.Prim

module _ (A : Type) (B : A → Type) where
  postulate
    a1 a2 : A
    p : a1 ≡ a2
    b1 : B a1
    b2 : B a2

  tyPathP : Type
  tyPathP = PathP (λ i → B (p i)) b1 b2

  pathPPrim : SqFill tyPathP
  pathPPrim = sqFill tyPathP

  pathPManual : SqFill tyPathP
  pathPManual = SqFillPathP (B a1) (B a2) b1 b2 (λ i → B (p i)) (sqFill (B a1))

  checkPathP : (λ {lu} {ld} → pathPPrim {lu} {ld}) ≡ pathPManual
  checkPathP i {lu} {ld} = pathPPrim {lu} {ld}
