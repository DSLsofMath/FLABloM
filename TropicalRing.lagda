\begin{code}

module TropicalRing where

open import Data.Nat renaming (_+_ to _+N_; _*_ to _*N_)
open import Relation.Binary.PropositionalEquality

open import Preliminaries

open import SemiNearRingRecord
open import SemiRingRecord
open import ClosedSemiRingRecord

data ℕ∞ : Set where
  D : ℕ → ℕ∞
  ∞ : ℕ∞

SDSNR : SemiNearRing
SDSNR = snr
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
  ⊓-assoc (suc x) (suc y) (suc z) rewrite ⊓-assoc x y z = refl

  assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
  assoc (D x) (D y) (D z)
    rewrite ⊓-assoc x y z = refl
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
  comm (D x) (D y) rewrite ⊓-comm x y = refl
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
  ⊓-idem (suc x) rewrite ⊓-idem x = refl

  idem : ∀ x → x + x ≡ x
  idem (D x) rewrite ⊓-idem x = refl
  idem ∞ = refl

  h1 : ∀ {x z} → x +N 0 ≡ (x +N 0) ⊓ (x +N suc z)
  h1 {zero} {zero} = refl
  h1 {zero} {suc z} = refl
  h1 {suc x} {zero} = cong suc (h1 {x} {0})
  h1 {suc x} {suc z} = cong suc (h1 {x} {suc z})

  distl-+-⊓ : ∀ x y z → (x +N y ⊓ z) ≡ ((x +N y) ⊓ (x +N z))
  distl-+-⊓ zero zero zero = refl
  distl-+-⊓ zero zero (suc z) = refl
  distl-+-⊓ zero (suc y) zero = refl
  distl-+-⊓ zero (suc y) (suc z) = refl
  distl-+-⊓ (suc x) zero zero rewrite ⊓-idem (x +N zero) = refl
  distl-+-⊓ (suc x) zero (suc z) = cong suc (h1 {x} {z})
  distl-+-⊓ (suc x) (suc y) zero rewrite ⊓-comm (x +N suc y) (x +N 0)
    = cong suc (h1 {x} {y})
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

  h3 : ∀ x z → (z +N suc (suc x)) ≡ suc (z +N suc x)
  h3 x zero = refl
  h3 x (suc z) = cong suc (h3 x z)

  h2 : ∀ x z → x ≡ x ⊓ (z +N suc x)
  h2 zero zero = refl
  h2 zero (suc z) = refl
  h2 (suc x) zero = cong suc (h2 x 0)
  h2 (suc x) (suc z) rewrite h3 x z = cong suc (h2 x (suc z))

  distr-+-⊓ : ∀ x y z → y ⊓ z +N x ≡ (y +N x) ⊓ (z +N x)
  distr-+-⊓ zero zero zero = refl
  distr-+-⊓ zero zero (suc z) = refl
  distr-+-⊓ zero (suc y) zero = refl
  distr-+-⊓ zero (suc y) (suc z) = cong suc (distr-+-⊓ zero y z)
  distr-+-⊓ (suc x) zero zero = cong suc (sym (⊓-idem x))
  distr-+-⊓ (suc x) zero (suc z) = cong suc (h2 x z)
  distr-+-⊓ (suc x) (suc y) zero rewrite ⊓-comm (y +N suc x) x = cong suc (h2 x y)
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

SDSR : SemiRing
SDSR = sr
  where

  open SemiNearRing SDSNR

  identl : ∀ x → D 0 *s x ≡ x
  identl (D x) = refl
  identl ∞ = refl

  +-identr : ∀ x → x +N 0 ≡ x
  +-identr zero = refl
  +-identr (suc x) = cong suc (+-identr x)

  identr : ∀ x → x *s D 0 ≡ x
  identr (D x) = cong D (+-identr x)
  identr ∞ = refl

  sr =
    record
      { snr = SDSNR
      ; ones = D 0
      ; *-identls = identl
      ; *-identrs = identr }

SDCSR : ClosedSemiRing
SDCSR = csr
  where

  open SemiRing SDSR
  open SemiNearRing snr
  open ClosedSemiRing using (Eq; Closure)

  open import Data.Product



  entire : ∀ a →
         ∃ (λ c → c ≡ ones +s (a *s c))
  entire (D x) = ones , refl
  entire ∞ = ones , refl

  csr =
    record
      { sr = SDSR
      ; entireQ = entire }

\end{code}
