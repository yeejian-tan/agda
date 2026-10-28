{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceUnitD where
open import CubicalUIP.Bench.Common
chk : Nice UnitD (λ x → x) (sqFill UnitD)
chk l r u d = refl
