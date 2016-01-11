\begin{code}

module ShortestDistance where

open import Data.Nat renaming (_+_ to _+N_; _*_ to _*N_)
open import Relation.Binary.PropositionalEquality

open import SemiNearRingRecord
open import SemiRingRecord
open import ClosedSemiRingRecord

data ShortestDistance : Set where
  Distance : ℕ → ShortestDistance
  Unreachable : ShortestDistance

SDSNR : SemiNearRing
SDSNR = snr
  where

  _+_ : ShortestDistance → ShortestDistance → ShortestDistance
  Distance x + Distance y = Distance (x ⊓ y)
  Distance x + Unreachable = Distance x
  Unreachable + Distance x = Distance x
  Unreachable + Unreachable = Unreachable

  _*_ : ShortestDistance → ShortestDistance → ShortestDistance
  Distance x * Distance y = Distance (x +N y)
  Distance x * Unreachable = Unreachable
  Unreachable * Distance x = Unreachable
  Unreachable * Unreachable = Unreachable

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
  assoc (Distance x) (Distance y) (Distance z)
    rewrite ⊓-assoc x y z = refl
  assoc (Distance x) (Distance x₁) Unreachable = refl
  assoc (Distance x) Unreachable (Distance x₁) = refl
  assoc (Distance x) Unreachable Unreachable = refl
  assoc Unreachable (Distance x) (Distance x₁) = refl
  assoc Unreachable (Distance x) Unreachable = refl
  assoc Unreachable Unreachable (Distance x) = refl
  assoc Unreachable Unreachable Unreachable = refl


  +-cong : ∀ {x y u v} → x ≡ y → u ≡ v → x + u ≡ y + v
  +-cong refl refl = refl

  semigroup =
    record
      { isEquivalence = isEquivalence
      ; assoc = assoc
      ; ∙-cong = +-cong }


  identl : ∀ x → Unreachable + x ≡ x
  identl (Distance x) = refl
  identl Unreachable = refl

  ⊓-comm : ∀ x y → (x ⊓ y) ≡ (y ⊓ x)
  ⊓-comm zero zero = refl
  ⊓-comm zero (suc y) = refl
  ⊓-comm (suc x) zero = refl
  ⊓-comm (suc x) (suc y) = cong suc (⊓-comm x y)

  comm : ∀ x y → x + y ≡ y + x
  comm (Distance x) (Distance y) rewrite ⊓-comm x y = refl
  comm (Distance x) Unreachable = refl
  comm Unreachable (Distance x) = refl
  comm Unreachable Unreachable = refl

  commMon =
    record
    { isSemigroup = semigroup
    ; identityˡ = identl
    ; comm = comm }


  zerol : ∀ x → Unreachable * x ≡ Unreachable
  zerol (Distance x) = refl
  zerol Unreachable = refl

  zeror : ∀ x → x * Unreachable ≡ Unreachable
  zeror (Distance x) = refl
  zeror Unreachable = refl

  _<*>_ : ∀ {x y u v} → x ≡ y → u ≡ v → x * u ≡ y * v
  refl <*> refl = refl

  ⊓-idem : ∀ x → x ⊓ x ≡ x
  ⊓-idem zero = refl
  ⊓-idem (suc x) rewrite ⊓-idem x = refl

  idem : ∀ x → x + x ≡ x
  idem (Distance x) rewrite ⊓-idem x = refl
  idem Unreachable = refl

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
  distl (Distance x) (Distance y) (Distance z) = cong Distance (distl-+-⊓ x y z)
  distl (Distance x) (Distance x₁) Unreachable = refl
  distl (Distance x) Unreachable (Distance x₁) = refl
  distl (Distance x) Unreachable Unreachable = refl
  distl Unreachable (Distance x) (Distance x₁) = refl
  distl Unreachable (Distance x) Unreachable = refl
  distl Unreachable Unreachable (Distance x) = refl
  distl Unreachable Unreachable Unreachable = refl

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
  distr (Distance x) (Distance y) (Distance z) = cong Distance (distr-+-⊓ x y z)
  distr (Distance x) (Distance x₁) Unreachable = refl
  distr (Distance x) Unreachable (Distance x₁) = refl
  distr (Distance x) Unreachable Unreachable = refl
  distr Unreachable (Distance x) (Distance x₁) = refl
  distr Unreachable (Distance x) Unreachable = refl
  distr Unreachable Unreachable (Distance x) = refl
  distr Unreachable Unreachable Unreachable = refl

  snr =
    record
      { s = ShortestDistance
      ; _≃s_ = _≡_
      ; zers = Unreachable
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

  identl : ∀ x → Distance 0 *s x ≡ x
  identl (Distance x) = refl
  identl Unreachable = refl

  +-identr : ∀ x → x +N 0 ≡ x
  +-identr zero = refl
  +-identr (suc x) = cong suc (+-identr x)

  identr : ∀ x → x *s Distance 0 ≡ x
  identr (Distance x) = cong Distance (+-identr x)
  identr Unreachable = refl

  sr =
    record
      { snr = SDSNR
      ; ones = Distance 0
      ; *-identls = identl
      ; *-identrs = identr }

SDCSR : ClosedSemiRing
SDCSR = csr
  where

  open SemiRing SDSR
  open SemiNearRing snr
  open import Data.Product

  entire : ∀ a →
         Σ ShortestDistance
         (λ c →
            Distance 0 +s (a *s c) ≡ c)
  entire (Distance x) = (Distance 0) , refl
  entire Unreachable = Distance 0 , refl

  csr =
    record
      { sr = SDSR
      ; entireQ = entire }

\end{code}
