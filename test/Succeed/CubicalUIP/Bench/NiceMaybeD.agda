{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceMaybeD where
open import CubicalUIP.Bench.Common
chk : ∀ {ℓ} (A : Type ℓ) → Nice A justD (sqFill (MaybeD A))
chk A l r u d = refl
