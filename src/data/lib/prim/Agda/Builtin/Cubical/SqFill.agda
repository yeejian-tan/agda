{-# OPTIONS --cubical=uip #-}

-- Square filling for --cubical=uip: prim^sqFill fills every square and computes by cases on
-- the type. The builtin SQFILL* proofs below are what it reduces to for Π, Σ, × and PathP.
-- Records, data types and universes are handled generically (records via their Σ of fields,
-- data types and universes by prim^sqFillData).
--
-- The proofs are developed in hset-cubical, one module per type former.

module Agda.Builtin.Cubical.SqFill where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path

SqFill : ∀{ℓ} → Type ℓ → Type ℓ
SqFill A =
  {a₀₀ : A} {a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ : A} {a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  → PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

{-# BUILTIN SQFILL SqFill #-}

primitive
  prim^sqFill : ∀ {ℓ} (A : Type ℓ) → SqFill A
  -- the data type and universe cases of prim^sqFill, which reduces to it
  prim^sqFillData : ∀ {ℓ} (A : Type ℓ) → SqFill A

-- not exported, to avoid clashes with libraries
module Helper where
  open import Agda.Builtin.Cubical.Path public
  open import Agda.Primitive.Cubical
    renaming ( primIMin       to infixr 20 _∧_  -- I → I → I
             ; primIMax       to infixr 20 _∨_  -- I → I → I
             ; primINeg       to infix 30 ~_ -- I → I
             ; primComp       to comp
             ; primHComp      to hcomp
             ; primTransp     to transp) public

  open import Agda.Primitive public renaming (Set   to Type)
  open import Agda.Builtin.Unit public
  open import Agda.Builtin.Cubical.Sub public
    renaming (primSubOut to outS)

  refl : ∀ {ℓ} {A : Type ℓ} {x : A} → x ≡ x
  refl {x = x} _ = x
  {-# INLINE refl #-}

   -- transport is a special case of transp
  transport : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
  transport p a = transp (λ i → p i) i0 a

  transportRefl : ∀ {ℓ} {A : Type ℓ} (x : A) → transport refl x ≡ x
  transportRefl {A = A} x i = transp (λ _ → A) i x

  transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) (x : A) → PathP (λ i → p i) x (transport p x)
  transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x

  SquareP : ∀ {ℓ}
    (A : I → I → Type ℓ)
    {a₀₀ : A i0 i0} {a₀₁ : A i0 i1} (a₀₋ : PathP (λ j → A i0 j) a₀₀ a₀₁)
    {a₁₀ : A i1 i0} {a₁₁ : A i1 i1} (a₁₋ : PathP (λ j → A i1 j) a₁₀ a₁₁)
    (a₋₀ : PathP (λ i → A i i0) a₀₀ a₁₀) (a₋₁ : PathP (λ i → A i i1) a₀₁ a₁₁)
    → Type ℓ
  SquareP A a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → PathP (λ j → A i j) (a₋₀ i) (a₋₁ i)) a₀₋ a₁₋

  cong : ∀{ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y : A} (f : (a : A) → B a) (p : x ≡ y) →
         PathP (λ i → B (p i)) (f x) (f y)
  cong f p i = f (p i)
  {-# INLINE cong #-}

  cong₂ : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {x y : A} {C : (a : A) → (b : B a) → Type ℓ''} →
          (f : (a : A) → (b : B a) → C a b) →
          (p : x ≡ y) →
          {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v) →
          PathP (λ i → C (p i) (q i)) (f x u) (f y v)
  cong₂ f p q i = f (p i) (q i)
  {-# INLINE cong₂ #-}

  Square : ∀{ℓ} {A : Type ℓ}
    {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
    {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
    (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
    → Type ℓ
  Square a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋

  _[_↦_] : ∀ {ℓ} (A : Type ℓ) (φ : I) (u : Partial φ A) → SSet ℓ
  A [ φ ↦ u ] = Sub A φ u

  infix 4 _[_↦_]

  J : ∀ {ℓ ℓ'} {A : Type ℓ} {x y : A} (P : ∀ y → x ≡ y → Type ℓ') (d : P x refl) (p : x ≡ y) → P y p
  J {x = x} P d p = transport (λ i → P (p i) (λ j → p (i ∧ j))) d

  JRefl : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A} (P : ∀ y → x ≡ y → Type ℓ') (d : P x refl) → J P d refl ≡ d
  JRefl P d = transportRefl d

  sym : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)
  {-# INLINE sym #-}

  data ⊥ : Type where

  ⊥-elim : ∀{ℓ} {A : Type ℓ} (x : ⊥) → A
  ⊥-elim ()

  record Lift {ℓa} ℓ (A : Type ℓa) : Type (ℓa ⊔ ℓ) where
    constructor lift
    field
      lower : A

  ⊥* : ∀{ℓ} → Type ℓ
  ⊥* = Lift _ ⊥

  ⊥*-elim : ∀{ℓ ℓ'} {A : Type ℓ} (x : ⊥* {ℓ'}) → A
  ⊥*-elim ()

  ⊤* : ∀{ℓ} → Type ℓ
  ⊤* = Lift _ ⊤

  tt* : ∀{ℓ} → ⊤* {ℓ}
  tt* = lift tt

  if_then_else_end : I → I → I → I
  if i then j else k end = (k ∧ (~ i ∨ j)) ∨ ((i ∨ k) ∧ j)

  {-# INLINE if_then_else_end #-}

  subst : ∀{ℓa ℓb} {A : Type ℓa} {a a' : A} (B : A → Type ℓb) (p : a ≡ a') → B a → B a'
  subst B p = transport (λ i → B (p i))

open Helper

module SqFillPi-proof where

  module _ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') (SqFillB : (x : A) → SqFill {ℓ = ℓ'} (B x)) where
    SqFillPi : SqFill {ℓ = ℓ ⊔ ℓ'} ((a : A) → B a)
    SqFillPi {lu} {ld} l {ru} {rd} r u d i j a =
        SqFillB a {lu a} {ld a} (λ i → l i a) {ru a} {rd a} (λ i → r i a) (λ i → u i a) (λ i → d i a) i j

  {-# BUILTIN SQFILLPI SqFillPi #-}

open SqFillPi-proof public using (SqFillPi)

module SqFillSigma-proof where
  open import Agda.Builtin.Sigma
  module _ {ℓ ℓ'} (A : Type ℓ) (SqFillA : SqFill A) (B : A → Type ℓ') (SqFillB : (x : A) → SqFill (B x)) where
    SqFillSigma : SqFill (Σ A (λ a → B a))
    SqFillSigma {lu} {ld} l {ru} {rd} r u d i j .fst = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
    SqFillSigma {lu} {ld} l {ru} {rd} r u d i j .snd = outS (sqb i j)
        where
        sqa : Square (cong fst l) (cong fst r) (cong fst u) (cong fst d)
        sqa = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d)

        spread : (i j i' j' : I) → sqa i j ≡ sqa i' j'
        spread i j i' j' k = sqa (if k then i' else i end) (if k then j' else j end)

        lub : B (sqa i0 i0)
        lub = snd lu
        lub' : B (sqa i j)
        lub' = transport (λ k → B (spread i0 i0 i j k)) lub
        LemmaLU : PathP (λ k → B (spread i0 i0 i j k)) lub lub'
        LemmaLU k = transp (λ l → B (spread i0 i0 i j (k ∧ l))) (~ k) lub

        ldb : B (fst ld)
        ldb = snd ld
        ldb' : B (sqa i j)
        ldb' = transport (λ k → B (spread i0 i1 i j k)) ldb
        LemmaLD : PathP (λ k → B (spread i0 i1 i j k)) ldb ldb'
        LemmaLD k = transp (λ l → B (spread i0 i1 i j (k ∧ l))) (~ k) ldb

        lb : PathP (λ k → B (spread i0 i0 i0 i1 k)) lub ldb
        lb = cong snd l
        lb' : PathP (λ k → B (spread i j i j k)) lub' ldb'
        lb' j' = comp (λ k → B (spread (k ∧ i) (k ∧ j) (k ∧ i) (~ k ∨ j) j'))
                        (λ where
                        k (j' = i0) → LemmaLU k
                        k (j' = i1) → LemmaLD k) (lb j')
        LemmaL : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (k' ∧ i) (~ k' ∨ j) k)) (LemmaLU k') (LemmaLD k')) lb lb'
        LemmaL k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (k' ∧ i) (~ k' ∨ j) k)) (LemmaLU k') (LemmaLD k')) lb k'

        rub : B (fst ru)
        rub = snd ru
        rub' : B (sqa i j)
        rub' = transport (λ k → B (spread i1 i0 i j k)) rub
        LemmaRU : PathP (λ k → B (spread i1 i0 i j k)) rub rub'
        LemmaRU k = transp (λ l → B (spread i1 i0 i j (k ∧ l))) (~ k) rub

        rdb : B (fst rd)
        rdb = snd rd
        rdb' : B (sqa i j)
        rdb' = transport (λ k → B (spread i1 i1 i j k)) rdb
        LemmaRD : PathP (λ k → B (spread i1 i1 i j k)) rdb rdb'
        LemmaRD k = transp (λ l → B (spread i1 i1 i j (k ∧ l))) (~ k) rdb

        rb : PathP (λ j → B (sqa i1 j)) rub rdb
        rb = cong snd r
        rb' : rub' ≡ rdb'
        rb' j' = comp (λ k → B (spread (~ k ∨ i) (k ∧ j) (~ k ∨ i) (~ k ∨ j) j'))
                        (λ where
                        k (j' = i0) → LemmaRU k
                        k (j' = i1) → LemmaRD k) (rb j')
        LemmaR : PathP (λ k' → PathP (λ k → B (spread (~ k' ∨ i) (k' ∧ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaRU k') (LemmaRD k')) rb rb'
        LemmaR k' = transport-filler (λ k' → PathP (λ k → B (spread (~ k' ∨ i) (k' ∧ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaRU k') (LemmaRD k')) rb k'

        ub : PathP (λ i → B (sqa i i0)) lub rub
        ub = cong snd u
        ub' : lub' ≡ rub'
        ub' i' = comp (λ k → B (spread (k ∧ i) (k ∧ j) (~ k ∨ i) (k ∧ j) i'))
                        (λ where
                        k (i' = i0) → LemmaLU k
                        k (i' = i1) → LemmaRU k) (ub i')
        LemmaU : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (~ k' ∨ i) (k' ∧ j) k)) (LemmaLU k') (LemmaRU k')) ub ub'
        LemmaU k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (k' ∧ j) (~ k' ∨ i) (k' ∧ j) k)) (LemmaLU k') (LemmaRU k')) ub k'

        db : PathP (λ i → B (sqa i i1)) ldb rdb
        db = cong snd d
        db' : ldb' ≡ rdb'
        db' i' = comp (λ k → B (spread (k ∧ i) (~ k ∨ j) (~ k ∨ i) (~ k ∨ j) i'))
                        (λ where
                        k (i' = i0) → LemmaLD k
                        k (i' = i1) → LemmaRD k) (db i')
        LemmaD : PathP (λ k' → PathP (λ k → B (spread (k' ∧ i) (~ k' ∨ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaLD k') (LemmaRD k')) db db'
        LemmaD k' = transport-filler (λ k' → PathP (λ k → B (spread (k' ∧ i) (~ k' ∨ j) (~ k' ∨ i) (~ k' ∨ j) k)) (LemmaLD k') (LemmaRD k')) db k'

        sqb-hollow : (i' j' : I) → Partial (i' ∨ j' ∨ ~ i' ∨ ~ j') (B (sqa i' j'))
        sqb-hollow i' j' (i' = i0) = l j' .snd
        sqb-hollow i' j' (i' = i1) = r j' .snd
        sqb-hollow i' j' (j' = i0) = u i' .snd
        sqb-hollow i' j' (j' = i1) = d i' .snd

        sqb'-hollow : (i' j' : I) → Partial (i' ∨ j' ∨ ~ i' ∨ ~ j') (B (sqa i j))
        sqb'-hollow i' j' (i' = i0) = lb' j'
        sqb'-hollow i' j' (i' = i1) = rb' j'
        sqb'-hollow i' j' (j' = i0) = ub' i'
        sqb'-hollow i' j' (j' = i1) = db' i'

        sqb' : (i' j' : I) → (B (sqa i j)) [ (i' ∨ j' ∨ ~ i' ∨ ~ j') ↦ sqb'-hollow i' j' ]
        sqb' i' j' = inS (SqFillB (sqa i j) lb' rb' ub' db' i' j')

        sqb : (i' j' : I) → (B (sqa i' j')) [ ( i' ∨ ~ i' ∨ j' ∨ ~ j' ) ↦ sqb-hollow i' j' ]
        sqb i' j' = inS (comp (λ k → B (spread i j i' j' k)) (
                        λ where
                            k (i' = i0) → LemmaL (~ k) j'
                            k (i' = i1) → LemmaR (~ k) j'
                            k (j' = i0) → LemmaU (~ k) i'
                            k (j' = i1) → LemmaD (~ k) i') (outS (sqb' i' j')))

  {-# BUILTIN SQFILLSIGMA SqFillSigma #-}

open SqFillSigma-proof public using (SqFillSigma)

module SqFillProduct-proof where
  open import Agda.Builtin.Product
  module _ {ℓ ℓ'} (A : Type ℓ) (SqFillA : SqFill A) (B : Type ℓ') (SqFillB : SqFill B) where
    SqFillProduct : SqFill (A × B)
    SqFillProduct {lu} {ld} l {ru} {rd} r u d i j .fst = SqFillA (cong fst l) (cong fst r) (cong fst u) (cong fst d) i j
    SqFillProduct {lu} {ld} l {ru} {rd} r u d i j .snd = SqFillB (cong snd l) (cong snd r) (cong snd u) (cong snd d) i j

  {-# BUILTIN SQFILLPRODUCT SqFillProduct #-}

open SqFillProduct-proof public using (SqFillProduct)

module SqFillPath-proof where
  module _ {ℓ} (A : Type ℓ) (a b : A) (SqFillA : SqFill A)  where
    SqFillPath : SqFill (a ≡ b)
    SqFillPath {lu} l r u d i j =
        hcomp (λ k → λ {(i = i0) → isPropa≡b lu (l j) k
                      ; (i = i1) → isPropa≡b lu (r j) k
                      ; (j = i0) → isPropa≡b lu (u i) k
                      ; (j = i1) → isPropa≡b lu (d i) k}) lu
        where
        isPropa≡b : (p q : a ≡ b) → p ≡ q
        isPropa≡b p q = SqFillA p q refl refl


  {-# BUILTIN SQFILLPATH SqFillPath #-}
  -- Only one of SqFillA or SqFillB is needed. Currently we request for both an only use SqFillA.
  module _ {ℓ} (A B : Type ℓ) (a : A) (b : B) (P : A ≡ B) (SqFillA : SqFill A) where
    SqFillPathP : SqFill (PathP (λ i → P i) a b)
    SqFillPathP {lu} l r u d i j =
        hcomp (λ k → λ {(i = i0) → isPropa≡b lu (l j) k
                      ; (i = i1) → isPropa≡b lu (r j) k
                      ; (j = i0) → isPropa≡b lu (u i) k
                      ; (j = i1) → isPropa≡b lu (d i) k}) lu
        where
        isPropa≡b : (p q : PathP (λ k → P k) a b) → p ≡ q
        isPropa≡b p q i k =
          comp (λ l → P (k ∧ l))
               (λ l → λ{(k = i0) → a ;
                        (k = i1) → transp (λ j → P (l ∨ (~ j))) l b ;
                        (i = i0) → wallp (~ l) k ;
                        (i = i1) → wallq (~ l) k })
               (SqFillA pa qa (refl {x = a}) (refl {x = transport (sym P) b}) i k)
          where
            pa : a ≡ transport (sym P) b
            pa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (p k)
            qa : a ≡ transport (sym P) b
            qa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (q k)

            wallp : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) p pa
            wallp l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (p k)
            wallq : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) q qa
            wallq l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (q k)

  {-# BUILTIN SQFILLPATHP SqFillPathP #-}

  -- TODO: can we request for (SqFill A ⊎ SqFill B) and have a term that adjusts?
  --   this then requires the filling to be done symmetrically wrt A and B (not too hard)
  -- module SqFillPathP' (A B : Type) (P : A ≡ B) (SqFillAorB : SqFill A ⊎ SqFill B) where
  --   SqFillPathP : {a : A} {b : B} → SqFill (PathP (λ i → P i) a b)
  --   SqFillPathP {a} {b} {lu} {ld} l r u d i j =
  --       hcomp (λ k → λ {(i = i0) → isPropa≡b lu (l j) k
  --                     ; (i = i1) → isPropa≡b lu (r j) k
  --                     ; (j = i0) → isPropa≡b lu (u i) k
  --                     ; (j = i1) → isPropa≡b lu (d i) k}) lu
  --       where
  --       isPropa≡b : {a : A} {b : B} (p q : PathP (λ k → P k) a b) → p ≡ q
  --       isPropa≡b {a} {b} p q i k =
  --         comp (λ l → P (k ∧ l))
  --              (λ l → λ{(k = i0) → a ;
  --                       (k = i1) → transp (λ j → P (l ∨ (~ j))) l b ;
  --                       (i = i0) → wallp (~ l) k ;
  --                       (i = i1) → wallq (~ l) k })
  --              (SqFillA pa qa (refl {x = a}) (refl {x = transport (sym P) b}) i k)
  --         where
  --           pa : a ≡ transport (sym P) b
  --           pa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (p k)
  --           qa : a ≡ transport (sym P) b
  --           qa k = transp (λ l → P ((~ l) ∧ k)) (~ k) (q k)

  --           wallp : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) p pa
  --           wallp l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (p k)
  --           wallq : PathP (λ l → PathP (λ k → P (k ∧ ~ l)) a (transp (λ k → P (~ l ∨ ~ k)) (~ l) b)) q qa
  --           wallq l k = transp (λ j → P (k ∧ ~ (l ∧ j))) (~ (k ∧ l)) (q k)

open SqFillPath-proof public using (SqFillPath; SqFillPathP)
