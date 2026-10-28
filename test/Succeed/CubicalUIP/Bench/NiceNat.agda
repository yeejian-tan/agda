{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceNat where
open import CubicalUIP.Bench.Common
chk : Nice ℕ (λ n → suc (suc n)) (sqFill ℕ)
chk l r u d = refl
