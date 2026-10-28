{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceMaybe where
open import CubicalUIP.Bench.Common
chk : ∀ {ℓ} (A : Type ℓ) → Nice A just (sqFill (Maybe A))
chk A l r u d = refl
