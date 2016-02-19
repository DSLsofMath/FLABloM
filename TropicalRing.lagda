\begin{code}

module TropicalRing where

open import Data.Nat renaming (_+_ to _+N_; _*_ to _*N_)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.EqReasoning as EqReasoning


open import Preliminaries

open import SemiNearRingRecord
open import SemiRingRecord
open import ClosedSemiRingRecord

data ℕ∞ : Set where
  D : ℕ → ℕ∞
  ∞ : ℕ∞

SNR : SemiNearRing
SNR = snr
  where

  _+_ : ℕ∞ → ℕ∞ → ℕ∞
  D x + D y = D (x ⊓ y)
  D x + ∞ = D x
  ∞ + D x = D x
  ∞ + ∞ = ∞

  _*_ : ℕ∞ → ℕ∞ → ℕ∞
  D x * D y = D (x +N y)
  D x * ∞ = ∞
  ∞ * D x = ∞
  ∞ * ∞ = ∞

  ⊓-assoc : ∀ x y z → ((x ⊓ y) ⊓ z) ≡ (x ⊓ (y ⊓ z))
  ⊓-assoc zero zero zero = refl
  ⊓-assoc zero zero (suc z) = refl
  ⊓-assoc zero (suc y) zero = refl
  ⊓-assoc zero (suc y) (suc z) = refl
  ⊓-assoc (suc x) zero zero = refl
  ⊓-assoc (suc x) zero (suc z) = refl
  ⊓-assoc (suc x) (suc y) zero = refl
  ⊓-assoc (suc x) (suc y) (suc z) = cong suc (⊓-assoc x y z)

  assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
  assoc (D x) (D y) (D z) = cong D (⊓-assoc x y z)
  assoc (D x) (D x₁) ∞ = refl
  assoc (D x) ∞ (D x₁) = refl
  assoc (D x) ∞ ∞ = refl
  assoc ∞ (D x) (D x₁) = refl
  assoc ∞ (D x) ∞ = refl
  assoc ∞ ∞ (D x) = refl
  assoc ∞ ∞ ∞ = refl


  +-cong : ∀ {x y u v} → x ≡ y → u ≡ v → x + u ≡ y + v
  +-cong refl refl = refl

  semigroup =
    record
      { isEquivalence = isEquivalence
      ; assoc = assoc
      ; ∙-cong = +-cong }


  identl : ∀ x → ∞ + x ≡ x
  identl (D x) = refl
  identl ∞ = refl

  ⊓-comm : ∀ x y → (x ⊓ y) ≡ (y ⊓ x)
  ⊓-comm zero zero = refl
  ⊓-comm zero (suc y) = refl
  ⊓-comm (suc x) zero = refl
  ⊓-comm (suc x) (suc y) = cong suc (⊓-comm x y)

  comm : ∀ x y → x + y ≡ y + x
  comm (D x) (D y) = cong D (⊓-comm x y)
  comm (D x) ∞ = refl
  comm ∞ (D x) = refl
  comm ∞ ∞ = refl

  commMon =
    record
    { isSemigroup = semigroup
    ; identityˡ = identl
    ; comm = comm }


  zerol : ∀ x → ∞ * x ≡ ∞
  zerol (D x) = refl
  zerol ∞ = refl

  zeror : ∀ x → x * ∞ ≡ ∞
  zeror (D x) = refl
  zeror ∞ = refl

  _<*>_ : ∀ {x y u v} → x ≡ y → u ≡ v → x * u ≡ y * v
  refl <*> refl = refl

  ⊓-idem : ∀ x → x ⊓ x ≡ x
  ⊓-idem zero = refl
  ⊓-idem (suc x) = cong suc (⊓-idem x)

  idem : ∀ x → x + x ≡ x
  idem (D x) = cong D (⊓-idem x)
  idem ∞ = refl

  distl-lem1 : ∀ x z → x +N 0 ≡ (x +N 0) ⊓ (x +N suc z)
  distl-lem1 zero zero = refl
  distl-lem1 zero (suc z) = refl
  distl-lem1 (suc x) zero = cong suc (distl-lem1 x 0)
  distl-lem1 (suc x) (suc z) = cong suc (distl-lem1 x (suc z))

  distl-+-⊓ : ∀ x y z → (x +N y ⊓ z) ≡ ((x +N y) ⊓ (x +N z))
  distl-+-⊓ zero zero zero = refl
  distl-+-⊓ zero zero (suc z) = refl
  distl-+-⊓ zero (suc y) zero = refl
  distl-+-⊓ zero (suc y) (suc z) = refl
  distl-+-⊓ (suc x) zero zero = cong suc (sym (⊓-idem (x +N zero)))
  distl-+-⊓ (suc x) zero (suc z) = cong suc (distl-lem1 x z)
  distl-+-⊓ (suc x) (suc y) zero =
    let open EqReasoning (setoid ℕ)
    in begin
      suc (x +N zero)
    ≈⟨ cong suc (distl-lem1 x y) ⟩
      suc ((x +N zero) ⊓ (x +N suc y))
    ≈⟨ cong suc (⊓-comm (x +N zero) (x +N suc y)) ⟩
      suc ((x +N suc y) ⊓ (x +N zero))
    ∎
  distl-+-⊓ (suc x) (suc y) (suc z) = cong suc (distl-+-⊓ x (suc y) (suc z))

  distl : ∀ x y z → x * (y + z) ≡ (x * y) + (x * z)
  distl (D x) (D y) (D z) = cong D (distl-+-⊓ x y z)
  distl (D x) (D x₁) ∞ = refl
  distl (D x) ∞ (D x₁) = refl
  distl (D x) ∞ ∞ = refl
  distl ∞ (D x) (D x₁) = refl
  distl ∞ (D x) ∞ = refl
  distl ∞ ∞ (D x) = refl
  distl ∞ ∞ ∞ = refl

  ⊓> : ∀ x u v → u ≡ v → x ⊓ u ≡ x ⊓ v
  ⊓> x u .u refl = refl

  distr-lem1 : ∀ z x → suc (z +N x) ≡ (z +N suc x)
  distr-lem1 zero x = refl
  distr-lem1 (suc z) x = cong suc (distr-lem1 z x)

  distr-lem2 : ∀ x z → x ≡ x ⊓ (z +N suc x)
  distr-lem2 zero zero = refl
  distr-lem2 zero (suc z) = refl
  distr-lem2 (suc x) zero = cong suc (distr-lem2 x 0)
  distr-lem2 (suc x) (suc z) =
    let open EqReasoning (setoid ℕ)
    in begin
      suc x
    ≈⟨ cong suc (distr-lem2 x (suc z)) ⟩
      suc (x ⊓ suc (z +N suc x))
    ≈⟨ cong suc (⊓> x (suc (z +N suc x)) (z +N suc (suc x)) (distr-lem1 z (suc x))) ⟩
      suc (x ⊓ (z +N suc (suc x)))
    ∎

  distr-+-⊓ : ∀ x y z → y ⊓ z +N x ≡ (y +N x) ⊓ (z +N x)
  distr-+-⊓ zero zero zero = refl
  distr-+-⊓ zero zero (suc z) = refl
  distr-+-⊓ zero (suc y) zero = refl
  distr-+-⊓ zero (suc y) (suc z) = cong suc (distr-+-⊓ zero y z)
  distr-+-⊓ (suc x) zero zero = cong suc (sym (⊓-idem x))
  distr-+-⊓ (suc x) zero (suc z) = cong suc (distr-lem2 x z)
  distr-+-⊓ (suc x) (suc y) zero =
    let open EqReasoning (setoid ℕ)
    in begin
      suc x
    ≈⟨ cong suc (distr-lem2 x y) ⟩
      suc (x ⊓ (y +N suc x))
    ≈⟨ cong suc (⊓-comm x (y +N suc x)) ⟩
      suc ((y +N suc x) ⊓ x)
    ∎
  distr-+-⊓ (suc x) (suc y) (suc z) = cong suc (distr-+-⊓ (suc x) y z)

  distr : ∀ x y z → (y + z) * x ≡ (y * x) + (z * x)
  distr (D x) (D y) (D z) = cong D (distr-+-⊓ x y z)
  distr (D x) (D x₁) ∞ = refl
  distr (D x) ∞ (D x₁) = refl
  distr (D x) ∞ ∞ = refl
  distr ∞ (D x) (D x₁) = refl
  distr ∞ (D x) ∞ = refl
  distr ∞ ∞ (D x) = refl
  distr ∞ ∞ ∞ = refl

  snr =
    record
      { s = ℕ∞
      ; _≃s_ = _≡_
      ; zers = ∞
      ; _+s_ = _+_
      ; _*s_ = _*_
      ; isCommMon = commMon
      ; zeroˡ = zerol
      ; zeroʳ = zeror
      ; _<*>_ = _<*>_
      ; idem = idem
      ; distl = distl
      ; distr = distr
      }

SR : SemiRing
SR = sr
  where

  open SemiNearRing SNR

  identl : ∀ x → D 0 *s x ≡ x
  identl (D x) = refl
  identl ∞ = refl

  open import Data.Nat.Properties.Simple using (+-assoc; +-right-identity)

  identr : ∀ x → x *s D 0 ≡ x
  identr (D x) = cong D (+-right-identity x)
  identr ∞ = refl

  assoc : ∀ x y z →
         (x *s y) *s z ≡
         x *s (y *s z)
  assoc (D x) (D x₁) (D x₂) = cong D (+-assoc x x₁ x₂)
  assoc (D x) (D x₁) ∞ = refl
  assoc (D x) ∞ (D x₁) = refl
  assoc (D x) ∞ ∞ = refl
  assoc ∞ (D x) (D x₁) = refl
  assoc ∞ (D x) ∞ = refl
  assoc ∞ ∞ (D x) = refl
  assoc ∞ ∞ ∞ = refl

  sr =
    record
      { snr = SNR
      ; ones = D 0
      ; *-assocs  = assoc
      ; *-identls = identl
      ; *-identrs = identr }

CSR : ClosedSemiRing
CSR = csr
  where

  open SemiRing SR
  open SemiNearRing snr
  open ClosedSemiRing using (Eq; Closure)

  open import Data.Product

  entire : ∀ a →
         ∃ (λ c → c ≡ ones +s (a *s c))
  entire (D x)  = ones , refl
  entire ∞      = ones , refl

  csr =
    record
      { sr = SR
      ; entireQ = entire }

\end{code}
