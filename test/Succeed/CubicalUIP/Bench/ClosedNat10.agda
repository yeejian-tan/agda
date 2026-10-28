{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.ClosedNat10 where
open import CubicalUIP.Bench.Common
xs : ℕ
xs = 10
chk : sqFill ℕ {xs} {xs} refl {xs} {xs} refl refl refl ≡ refl
chk _ _ _ = xs
