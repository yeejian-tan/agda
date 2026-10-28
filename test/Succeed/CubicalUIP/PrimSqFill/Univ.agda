{-# OPTIONS --cubical=uip #-}

-- prim^sqFill at a universe: squares of types are filled by cases on the type formers of the
-- edges (in the implementation only, there is no typecase).

module CubicalUIP.PrimSqFill.Univ where

open import CubicalUIP.Prim
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Reflection
  using (Term; TC; Name; bindTC; normalise; unify; typeError; strErr; termErr; nameErr; con; pi; def;
         primQNameEquality)

-- Types have no eta, so a reduct can be checked with refl. Where the reduct is too big to
-- write down, check the head of its normal form instead.
notReducedTo : Name → Term → TC ⊤
notReducedTo q t = typeError (strErr "did not reduce to" ∷ nameErr q ∷ termErr t ∷ [])

checkDef : Bool → Name → Term → Term → TC ⊤
checkDef true  _ _ hole = unify hole (con (quote tt) [])
checkDef false q t _    = notReducedTo q t

macro
  reducesToPi : Term → Term → TC ⊤
  reducesToPi t hole = bindTC (normalise t) λ where
    (pi _ _) → unify hole (con (quote tt) [])
    t'       → typeError (strErr "did not reduce to a Π type:" ∷ termErr t' ∷ [])

  reducesToDef : Name → Term → Term → TC ⊤
  reducesToDef q t hole = bindTC (normalise t) λ where
    t'@(def q' _) → checkDef (primQNameEquality q q') q t' hole
    t'            → notReducedTo q t'

-- Constant edges at a neutral type: the constant square.
module Constant (X : Type) where

  check : sqFill Type {X} {X} refl {X} {X} refl refl refl ≡ refl
  check _ _ _ = X

-- Squares of types along a square of points in A.
module Formers (A : Type) (B : A → Type) {x₀₀ x₀₁ x₁₀ x₁₁ : A}
       (l : x₀₀ ≡ x₀₁) (r : x₁₀ ≡ x₁₁) (u : x₀₀ ≡ x₁₀) (d : x₀₁ ≡ x₁₁) where

  -- the square of points in A, pushed through a type former
  along : (F : A → Type) → PathP (λ i → F (u i) ≡ F (d i)) (cong F l) (cong F r)
  along F = sqFill Type (cong F l) (cong F r) (cong F u) (cong F d)

  -- a data type former: the level is constant, the square is pushed into the parameter
  checkList : along (λ a → List (B a)) ≡ (λ i j → List (sqFill Type (cong B l) (cong B r) (cong B u) (cong B d) i j))
  checkList = refl

  -- Π, with a varying domain and codomain
  F : A → Type
  F a = B a → Nat → B a

  module _ (i j : I) where
    checkPi : ⊤
    checkPi = reducesToPi (along F i j)

    -- PathP, here the non-dependent paths in A between varying endpoints
    checkPathP : ⊤
    checkPathP = reducesToDef PathP (along (λ a → a ≡ a) i j)

  -- the boundary of the reduced squares holds definitionally
  checkPiL : (λ j → along F i0 j) ≡ cong F l
  checkPiL = refl

  checkPiD : (λ i → along F i i1) ≡ cong F d
  checkPiD = refl

  checkPathPL : (λ j → along (λ a → a ≡ a) i0 j) ≡ cong (λ a → a ≡ a) l
  checkPathPL = refl

  checkPathPU : (λ i → along (λ a → a ≡ a) i i0) ≡ cong (λ a → a ≡ a) u
  checkPathPU = refl

-- Edges that are not headed by a type former stay stuck, which must not break anything.
module Stuck {X₀₀ X₀₁ X₁₀ X₁₁ : Type}
       (l : X₀₀ ≡ X₀₁) (r : X₁₀ ≡ X₁₁) (u : X₀₀ ≡ X₁₀) (d : X₀₁ ≡ X₁₁) where

  sq = sqFill Type l r u d
