{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.ClosedListD5 where
open import CubicalUIP.Bench.Common
rep : ℕ → ListD UnitD
rep zero = nilD
rep (suc n) = _∷D_ ttD (rep n)
xs : ListD UnitD
xs = rep 5
chk : sqFill (ListD UnitD) {xs} {xs} refl {xs} {xs} refl refl refl ≡ refl
chk _ _ _ = xs
