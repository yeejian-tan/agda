{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.ClosedNatD160 where
open import CubicalUIP.Bench.Common
toD : ℕ → NatD
toD zero = zeroD
toD (suc n) = sucD (toD n)
xs : NatD
xs = toD 160
chk : sqFill NatD {xs} {xs} refl {xs} {xs} refl refl refl ≡ refl
chk _ _ _ = xs
