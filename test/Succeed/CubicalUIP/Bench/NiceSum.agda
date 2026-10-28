{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceSum where
open import CubicalUIP.Bench.Common
chk : ∀ {ℓ} (A B : Type ℓ) → Nice A (inl {B = B}) (sqFill (A ⊎ B))
chk A B l r u d = refl
