{-# OPTIONS --cubical=uip #-}

-- hcomp at a universe computes by the type formers of the base and the tubes: if they all have
-- the same head, the composition is pushed into the arguments.

module CubicalUIP.HCompType where

open import CubicalUIP.Prim
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
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

-- Heads without arguments: the base.
module Atomic (A : Type) (i : I) where

  checkBool : hcomp (λ k → λ { (i = i0) → Bool ; (i = i1) → Bool }) Bool ≡ Bool
  checkBool = refl

  checkVar : hcomp (λ k → λ { (i = i0) → A ; (i = i1) → A }) A ≡ A
  checkVar = refl

  checkType : hcomp (λ k → λ { (i = i0) → Type ; (i = i1) → Type }) Type ≡ Type
  checkType = refl

-- Composites of lines of types: transport along them computes.
module Transport where

  line : I → Type
  line i = hcomp (λ k → λ { (i = i0) → Bool ; (i = i1) → Bool }) Bool

  check : transport (λ i → line i) true ≡ true
  check = refl

-- Data types: the composition is pushed into the parameters.
module Data {ℓ} {A A' : Type ℓ} (p : A ≡ A') (i : I) where

  checkList : hcomp (λ k → λ { (i = i0) → List A ; (i = i1) → List (p k) }) (List A)
            ≡ List (hcomp (λ k → λ { (i = i0) → A ; (i = i1) → p k }) A)
  checkList = refl

-- Π and records: the composition is pushed into the arguments (the codomain then contains
-- transports, so only check the head).
module Formers {A A' B B' : Type} (p : A ≡ A') (q : B ≡ B') (i : I) where

  checkPi : ⊤
  checkPi = reducesToPi (hcomp (λ k → λ { (i = i0) → (A → B) ; (i = i1) → (p k → q k) }) (A → B))

  checkSigma : ⊤
  checkSigma = reducesToDef Σ
    (hcomp (λ k → λ { (i = i0) → Σ A (λ _ → B) ; (i = i1) → Σ (p k) (λ _ → q k) }) (Σ A (λ _ → B)))

-- Different heads, or neutral heads with arguments, stay stuck, which must not break anything.
module Stuck {A B : Type} (p : A ≡ B) (F : Type → Type) (i : I) where

  differentHeads : Type
  differentHeads = hcomp (λ k → λ { (i = i0) → A ; (i = i1) → p k }) A

  neutralHead : Type
  neutralHead = hcomp (λ k → λ { (i = i0) → F A ; (i = i1) → F A }) (F A)
