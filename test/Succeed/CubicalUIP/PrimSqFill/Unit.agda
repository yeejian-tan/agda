{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.Unit where

open import CubicalUIP.Prim
open import Agda.Builtin.Unit

unitPrim : SqFill ⊤
unitPrim = sqFill ⊤

unitManual : SqFill ⊤
unitManual = SqFillUnit

checkUnit : (λ {lu} {ld} → unitPrim {lu} {ld}) ≡ unitManual
checkUnit _ = unitPrim
