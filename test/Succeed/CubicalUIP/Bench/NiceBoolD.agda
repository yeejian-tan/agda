{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceBoolD where
open import CubicalUIP.Bench.Common
chk : sqFill BoolD {trueD} {trueD} refl {trueD} {trueD} refl refl refl ≡ refl
chk = refl
