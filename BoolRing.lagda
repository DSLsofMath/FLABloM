\begin{code}
module BoolRing where

open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import SemiNearRingRecord
open import SemiRingRecord
open import ClosedSemiRingRecord

BoolSNR : SemiNearRing
BoolSNR = snr
  where

  assoc : ∀ x y z → (x ∨ y) ∨ z ≡ x ∨ y ∨ z
  assoc true true true = refl
  assoc true true false = refl
  assoc true false true = refl
  assoc true false false = refl
  assoc false true true = refl
  assoc false true false = refl
  assoc false false true = refl
  assoc false false false = refl

  +-cong : ∀ {x y u v} → x ≡ y → u ≡ v → x ∨ u ≡ y ∨ v
  +-cong refl refl = refl

  semigroup =
    record
      { isEquivalence = isEquivalence
      ; assoc = assoc
      ; ∙-cong = +-cong }

  identl : ∀ (x : Bool) → x ≡ x
  identl true = refl
  identl false = refl

  comm : ∀ x y → x ∨ y ≡ y ∨ x
  comm true true = refl
  comm true false = refl
  comm false true = refl
  comm false false = refl

  commMon =
    record
      { isSemigroup = semigroup
      ; identityˡ = identl
      ; comm = comm }

  zeror : ∀ x → x ∧ false ≡ false
  zeror true = refl
  zeror false = refl

  _<*>_ : ∀ {x y u v} → x ≡ y → u ≡ v → x ∧ u ≡ y ∧ v
  refl <*> refl = refl

  idem : ∀ x → x ∨ x ≡ x
  idem true = refl
  idem false = refl

  distl : ∀ x y z → x ∧ (y ∨ z) ≡ x ∧ y ∨ x ∧ z
  distl true true true = refl
  distl true true false = refl
  distl true false true = refl
  distl true false false = refl
  distl false true true = refl
  distl false true false = refl
  distl false false true = refl
  distl false false false = refl

  distr : ∀ x y z → (y ∨ z) ∧ x ≡ y ∧ x ∨ z ∧ x
  distr true true true = refl
  distr true true false = refl
  distr true false true = refl
  distr true false false = refl
  distr false true true = refl
  distr false true false = refl
  distr false false true = refl
  distr false false false = refl

  snr =
    record
      { s = Bool
      ; _≃s_ = _≡_
      ; zers = false
      ; _+s_ = _∨_
      ; _*s_ = _∧_
      ; isCommMon = commMon
      ; zeroˡ = λ x → refl
      ; zeroʳ = zeror
      ; _<*>_ = _<*>_
      ; idem = idem
      ; distl = distl
      ; distr = distr
      }

BoolSR : SemiRing
BoolSR = sr
  where

  identr : ∀ x → x ∧ true ≡ x
  identr true = refl
  identr false = refl

  sr =
    record
    { snr = BoolSNR
    ; ones = true
    ; *-identls = λ x → refl
    ; *-identrs = identr }

BoolCSR : ClosedSemiRing
BoolCSR = csr
  where

  open import Data.Product

  entire : (a : Bool) → Σ Bool (_≡_ true)
  entire true = true , refl
  entire false = true , refl

  csr =
    record
      { sr = BoolSR
      ; entireQ = entire }

\end{code}
