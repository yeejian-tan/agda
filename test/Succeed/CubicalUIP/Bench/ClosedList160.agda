{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.ClosedList160 where
open import CubicalUIP.Bench.Common
rep : ℕ → List UnitD
rep zero = []
rep (suc n) = _∷_ ttD (rep n)
xs : List UnitD
xs = rep 160
chk : sqFill (List UnitD) {xs} {xs} refl {xs} {xs} refl refl refl ≡ refl
chk _ _ _ = xs
