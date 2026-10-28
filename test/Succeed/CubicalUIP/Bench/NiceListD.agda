{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceListD where
open import CubicalUIP.Bench.Common
chk : ∀ {ℓ} (A : Type ℓ) → Nice A (λ a → a ∷D (a ∷D nilD)) (sqFill (ListD A))
chk A l r u d = refl
