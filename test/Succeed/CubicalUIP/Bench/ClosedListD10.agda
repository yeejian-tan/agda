{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.ClosedListD10 where
open import CubicalUIP.Bench.Common
rep : ℕ → ListD UnitD
rep zero = nilD
rep (suc n) = _∷D_ ttD (rep n)
xs : ListD UnitD
xs = rep 10
chk : sqFill (ListD UnitD) {xs} {xs} refl {xs} {xs} refl refl refl ≡ refl
chk _ _ _ = xs
