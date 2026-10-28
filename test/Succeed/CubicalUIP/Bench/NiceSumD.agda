{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceSumD where
open import CubicalUIP.Bench.Common
chk : ∀ {ℓ} (A B : Type ℓ) → Nice A (inlD {B = B}) (sqFill (A ⊎D B))
chk A B l r u d = refl
