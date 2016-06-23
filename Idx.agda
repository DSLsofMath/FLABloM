module Idx where

open import Shape
open import Product
open import Matrix

-- Index indexed by what shape it indexes
data Idx : Shape →  Set where
  Bl : ∀ {l r} → Idx l → Idx (B l r)
  Br : ∀ {l r} → Idx r → Idx (B l r)
  ∙ : Idx L

-- Index into a matrix
idx : {a : Set} {rs cs : Shape} (m : M a rs cs) (r : Idx rs) (c : Idx cs) → a
idx (One x) ∙ ∙ = x
idx (Row m m₁) ∙ (Bl c) = idx m ∙ c
idx (Row m m₁) ∙ (Br c) = idx m₁ ∙ c
idx (Col m m₁) (Bl r) ∙ = idx m r ∙
idx (Col m m₁) (Br r) ∙ = idx m₁ r ∙
idx (Q m m₁ m₂ m₃) (Bl r) (Bl c) = idx m r c
idx (Q m m₁ m₂ m₃) (Bl r) (Br c) = idx m₁ r c
idx (Q m m₁ m₂ m₃) (Br r) (Bl c) = idx m₂ r c
idx (Q m m₁ m₂ m₃) (Br r) (Br c) = idx m₃ r c
