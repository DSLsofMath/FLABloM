module FromVec where

open import Data.Vec
open import Data.Nat

open import Shape
open import Matrix

fromVec : ∀ {a} (sh sh2 : Shape) → Vec a (toNat sh * toNat sh2) → M a sh sh2
fromVec sh sh2 v with tonat sh * toNat sh2
fromVec sh sh2 v | n = {!!} -- but there is a zero case suddenly, which sould be impossible
