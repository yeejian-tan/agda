{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.NiceUnit where
open import CubicalUIP.Bench.Common
chk : Nice ⊤ (λ x → x) (sqFill ⊤)
chk l r u d = refl
