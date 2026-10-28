{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.ClosedNat5 where
open import CubicalUIP.Bench.Common
xs : ℕ
xs = 5
chk : sqFill ℕ {xs} {xs} refl {xs} {xs} refl refl refl ≡ refl
chk _ _ _ = xs
