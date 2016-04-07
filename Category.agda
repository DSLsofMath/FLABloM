module Category where

open import Level
open import Relation.Binary
open import Relation.Binary.Core

record Category {ol al l} : Set (suc (ol ⊔ al ⊔ l)) where
  field
    ob : Set ol
    arr : ob → ob → Set al

    id : ∀ {a} → arr a a
    _∘_ : ∀ {a b c} → arr b c → arr a b → arr a c
    _≈_ : ∀ {a b} → Rel (arr a b) l

  infixr 50 _≈_
  infixr 60 _∘_

  field
    isEquivalence : {a b : ob} → IsEquivalence {al} {l} {arr a b} _≈_
    idL : ∀ {a b} {f : arr a b} → id ∘ f ≈ f
    idR : ∀ {a b} {f : arr a b} → f ∘ id ≈ f
    <∘> : ∀ {a b c} {f g : arr a b} {h i : arr b c} →
      f ≈ g → h ≈ i → h ∘ f ≈ i ∘ g
    assoc : ∀ {a b c d} {f : arr c d} {g : arr b c} {h : arr a b} →
      f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
