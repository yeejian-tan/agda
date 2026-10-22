{-# OPTIONS --cubical=uip #-}

module CubicalUIP.PrimSqFill.Bool where

open import CubicalUIP.Prim
open import Agda.Builtin.Bool

boolPrim : SqFill Bool
boolPrim = sqFill Bool

boolManual : SqFill Bool
boolManual = SqFillBool

checkBool : (λ {lu} {ld} → boolPrim {lu} {ld}) ≡ boolManual
checkBool _ = boolPrim
