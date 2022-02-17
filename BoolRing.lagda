\begin{code}
module BoolRing where

open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import SemiNearRingRecord
open import SemiRingRecord
open import ClosedSemiRingRecord
open import Algebra.Structures           using (IsSemigroup; IsCommutativeMonoid)

assoc : ∀ x y z →  (x ∨ y) ∨ z ≡ x ∨ (y ∨ z)
assoc true   true   true   = refl
assoc true   true   false  = refl
assoc true   false  true   = refl
assoc true   false  false  = refl
assoc false  true   true   = refl
assoc false  true   false  = refl
assoc false  false  true   = refl
assoc false  false  false  = refl

+-cong : ∀ {x y u v} → x ≡ y → u ≡ v → x ∨ u ≡ y ∨ v
+-cong refl refl = refl

semigroup : IsSemigroup _≡_ _∨_
semigroup =
  record
    { isMagma = record { isEquivalence = isEquivalence
                       ; ∙-cong = +-cong }
    ; assoc = assoc}

-- identl : ∀ (x : Bool) → x ≡ x
-- identl true   = refl
-- identl false  = refl

identl : ∀ (x : Bool) → x ∨ false ≡ x
identl false  = refl
identl true   = refl

comm : ∀ x y → x ∨ y ≡ y ∨ x
comm true   true   = refl
comm true   false  = refl
comm false  true   = refl
comm false  false  = refl

open import Data.Product using (Σ; _,_)
commMon : IsCommutativeMonoid _≡_ _∨_ false
commMon =
  record
    { isMonoid = record { isSemigroup = semigroup
                        ; identity = (λ x → refl) , identl
                        }
    ; comm = comm
    }

zeror : ∀ x → x ∧ false ≡ false
zeror true   = refl
zeror false  = refl

_<*>_ : ∀ {x y u v} → x ≡ y → u ≡ v → x ∧ u ≡ y ∧ v
refl <*> refl = refl

idem : ∀ x → x ∨ x ≡ x
idem true   = refl
idem false  = refl

distl : ∀ x y z → x ∧ (y ∨ z) ≡ (x ∧ y) ∨ (x ∧ z)
distl true   true   true   = refl
distl true   true   false  = refl
distl true   false  true   = refl
distl true   false  false  = refl
distl false  true   true   = refl
distl false  true   false  = refl
distl false  false  true   = refl
distl false  false  false  = refl

distr : ∀ x y z → (y ∨ z) ∧ x ≡ (y ∧ x) ∨ (z ∧ x)
distr true   true   true   = refl
distr true   true   false  = refl
distr true   false  true   = refl
distr true   false  false  = refl
distr false  true   true   = refl
distr false  true   false  = refl
distr false  false  true   = refl
distr false  false  false  = refl

BoolSNR : SemiNearRing
BoolSNR = record
  {  s          = Bool
  ;  _≃s_       = _≡_
  ;  zers       = false
  ;  _+s_       = _∨_
  ;  _*s_       = _∧_
  ;  isCommMon  = commMon
  ;  zeroˡ      = λ x → refl
  ;  zeroʳ      = zeror
  ;  _<*>_      = _<*>_
  ;  idem       = idem
  ;  distl      = distl
  ;  distr      = distr
  }

identr : ∀ x → x ∧ true ≡ x
identr true   = refl
identr false  = refl

assocs : ∀ x y z → (x ∧ y) ∧ z ≡ x ∧ (y ∧ z)
assocs true   true   true   = refl
assocs true   true   false  = refl
assocs true   false  true   = refl
assocs true   false  false  = refl
assocs false  true   true   = refl
assocs false  true   false  = refl
assocs false  false  true   = refl
assocs false  false  false  = refl

BoolSR : SemiRing
BoolSR = record
  {  snr        = BoolSNR
  ;  ones       = true
  ;  *-assocs   = assocs
  ;  *-identls  = λ x → refl
  ;  *-identrs  = identr
  }

entire : Bool → Σ Bool (λ c → c ≡ true)
entire true   = true , refl
entire false  = true , refl

BoolCSR : ClosedSemiRing
BoolCSR = record
  {  sr       = BoolSR
  ;  entireQ  = entire
  }
\end{code}
