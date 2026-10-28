{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceList where
open import CubicalUIP.Bench.Common
chk : ∀ {ℓ} (A : Type ℓ) → Nice A (λ a → a ∷ (a ∷ [])) (sqFill (List A))
chk A l r u d = refl
