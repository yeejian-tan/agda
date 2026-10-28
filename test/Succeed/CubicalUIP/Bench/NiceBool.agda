{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceBool where
open import CubicalUIP.Bench.Common
chk : sqFill Bool {true} {true} refl {true} {true} refl refl refl ≡ refl
chk = refl
