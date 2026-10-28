{-# OPTIONS --cubical=uip #-}
module CubicalUIP.Bench.Neutral where
open import CubicalUIP.Bench.Common
postulate A : Type ; x y : A ; xs ys : List A ; xsD ysD : ListD A ; n : ℕ
postulate p : x ∷ xs ≡ y ∷ ys ; pD : x ∷D xsD ≡ y ∷D ysD ; q : suc n ≡ suc n ; qD : sucD zeroD ≡ sucD zeroD
sq  = sqFill (List A) p p refl refl
sqD = sqFill (ListD A) pD pD refl refl
sqN = sqFill ℕ q q refl refl
sqND = sqFill NatD qD qD refl refl
