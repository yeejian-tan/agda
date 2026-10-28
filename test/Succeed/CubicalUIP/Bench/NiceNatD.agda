{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceNatD where
open import CubicalUIP.Bench.Common
chk : Nice NatD (λ n → sucD (sucD n)) (sqFill NatD)
chk l r u d = refl
