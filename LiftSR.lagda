\begin{code}
open import SemiRingRecord

module LiftSR (sr : SemiRing) where

open import Shape
open import Matrix

open import Algebra.Structures
open import Relation.Binary
open import Data.Product hiding (swap)
import Relation.Binary.EqReasoning as EqReasoning


open import SemiNearRingRecord

open SemiRing sr
open SemiNearRing snr

open import LiftSNR snr renaming (Square to SquareSNR) public

oneS : {shape : Shape} → M s shape shape
oneS {L}               =  One ones
oneS {B shape shape₁}  =  Q oneS       (zerS _ _)
                          (zerS _ _)   oneS

*-identlS : {r c : Shape} (x : M s r c) → (oneS *S x) ≃S x
*-identlS {L}      {L}      (One x)    = *-identls x
*-identlS {L}      {B c c₁} (Row x x₁) = *-identlS x , *-identlS x₁
*-identlS {B r r₁} {L}      (Col x x₁) =
  (let open EqReasoning setoidS
  in begin
    oneS *S x +S zerS r r₁ *S x₁
  ≈⟨ <+S> r L (*-identlS x) (zeroSˡ r r₁ L x₁) ⟩
    x +S zerS r L
  ≈⟨ identSʳ r L x ⟩
    x
  ∎) ,
  (let open EqReasoning setoidS
  in begin
    zerS r₁ r *S x +S oneS *S x₁
  ≈⟨ <+S> r₁ L (zeroSˡ r₁ r L x) (*-identlS x₁) ⟩
    zerS r₁ L +S x₁
  ≈⟨ identSˡ r₁ L x₁ ⟩
    x₁
  ∎)
*-identlS {B r r₁} {B c c₁} (Q x x₁ x₂ x₃) =
  -- oneS *S x +S zerS r r₁ *S x₂ ≃S x
  (let open EqReasoning setoidS
  in begin
    oneS *S x +S zerS r r₁ *S x₂
  ≈⟨ <+S> r c (*-identlS x) (zeroSˡ r r₁ c x₂) ⟩
    x +S zerS r c
  ≈⟨ identSʳ r c x ⟩
    x
  ∎) ,
  -- oneS *S x₁ +S zerS r r₁ *S x₃ ≃S x₁
  (let open EqReasoning setoidS
  in begin
    oneS *S x₁ +S zerS r r₁ *S x₃
  ≈⟨ <+S> r c₁ (*-identlS x₁) (zeroSˡ r r₁ c₁ x₃) ⟩
    x₁ +S zerS r c₁
  ≈⟨ identSʳ r c₁ x₁ ⟩
    x₁
  ∎) ,
  (let open EqReasoning setoidS
  in begin
    zerS r₁ r *S x +S oneS *S x₂
  ≈⟨ <+S> r₁ c (zeroSˡ r₁ r c x) (*-identlS x₂) ⟩
    zerS r₁ c +S x₂
  ≈⟨ identSˡ r₁ c x₂ ⟩
    x₂
  ∎) ,
  (let open EqReasoning setoidS
  in begin
    zerS r₁ r *S x₁ +S oneS *S x₃
  ≈⟨ <+S> r₁ c₁ (zeroSˡ r₁ r c₁ x₁) (*-identlS x₃) ⟩
    zerS r₁ c₁ +S x₃
  ≈⟨ identSˡ r₁ c₁ x₃ ⟩
    x₃
  ∎)

*-identrS : {r c : Shape} (x : M s r c) → (x *S oneS) ≃S x
*-identrS {L} {L} (One x) = *-identrs x
*-identrS {L} {B c c₁} (Row x x₁) =
  (let open EqReasoning setoidS
  in begin
    x *S oneS +S x₁ *S zerS c₁ c
  ≈⟨ <+S> L c (*-identrS x) (zeroSʳ L c₁ c x₁) ⟩
    x +S zerS L c
  ≈⟨ identSʳ L c x ⟩
    x
  ∎) ,
  (let open EqReasoning setoidS
  in begin
    x *S zerS c c₁ +S x₁ *S oneS
  ≈⟨ <+S> L c₁ (zeroSʳ L c c₁ x) (*-identrS x₁) ⟩
    zerS L c₁ +S x₁
  ≈⟨ identSˡ L c₁ x₁ ⟩
    x₁
  ∎)
*-identrS {B r r₁} {L} (Col x x₁) = *-identrS x , *-identrS x₁
*-identrS {B r r₁} {B c c₁} (Q x x₁ x₂ x₃) =
  (let open EqReasoning setoidS
  in begin
    x *S oneS +S x₁ *S zerS c₁ c
  ≈⟨ <+S> r c (*-identrS x) (zeroSʳ r c₁ c x₁) ⟩
    x +S zerS r c
  ≈⟨ identSʳ r c x ⟩
    x
  ∎) ,
  (let open EqReasoning setoidS
  in begin
    x *S zerS c c₁ +S x₁ *S oneS
  ≈⟨ <+S> r c₁ (zeroSʳ r c c₁ x) (*-identrS x₁) ⟩
    zerS r c₁ +S x₁
  ≈⟨ identSˡ r c₁ x₁ ⟩
    x₁
  ∎) ,
  (let open EqReasoning setoidS
  in begin
    x₂ *S oneS +S x₃ *S zerS c₁ c
  ≈⟨ <+S> r₁ c (*-identrS x₂) (zeroSʳ r₁ c₁ c x₃) ⟩
    x₂ +S zerS r₁ c
  ≈⟨ identSʳ r₁ c x₂ ⟩
    x₂
  ∎) ,
  (let open EqReasoning setoidS
  in begin
     x₂ *S zerS c c₁ +S x₃ *S oneS
  ≈⟨ <+S> r₁ c₁ (zeroSʳ r₁ c c₁ x₂) (*-identrS x₃) ⟩
    zerS r₁ c₁ +S x₃
  ≈⟨ identSˡ r₁ c₁ x₃ ⟩
    x₃
  ∎)

*-assoc-lemma1 : ∀ {r m1 m2 m3 c} (x : M s r m1)
  (y : M s m1 m2) (z : M s m2 c)
  (b : M s m1 m3) (c : M s m3 c) →
  (x *S y) *S z +S (x *S b) *S c ≃S x *S (y *S z +S b *S c)

*-assoc-lemma2 : ∀ {r m1 m2 m3 c}
  (x : M s r m1) (y : M s m1 m3)
  (a : M s r m2) (b : M s m2 m3)
  (z : M s m3 c) →
  (x *S y +S a *S b) *S z ≃S x *S y *S z +S a *S b *S z

*-assocS : ∀ sh1 sh2 sh3 sh4 (x : M s sh1 sh2) (y : M s sh2 sh3) (z : M s sh3 sh4)
  → ((x *S y) *S z) ≃S x *S y *S z

*-assocS .L .L .L .L (One x) (One y) (One z) = *-assocs x y z
*-assocS .L .L .L (B s1 s2) (One x) (One y) (Row z1 z2) =
  *-assocS  L L L s1 (One x) (One y) z1 ,
  *-assocS L L L s2 (One x) (One y) z2

*-assocS .L .L (B s1 s2) .L (One x) (Row y1 y2) (Col z1 z2) =
  let open EqReasoning setoidS
  in begin
    (One x *S y1) *S z1 +S (One x *S y2) *S z2
  ≈⟨ <+S> L L
          {(One x *S y1) *S z1} {One x *S y1 *S z1}
          {(One x *S y2) *S z2} {One x *S y2 *S z2}
          (*-assocS L L s1 L (One x) y1 z1)
          (*-assocS L L s2 L (One x) y2 z2) ⟩
    One x *S y1 *S z1 +S One x *S y2 *S z2
  ≈⟨ symS L L
          {One x *S Row y1 y2 *S Col z1 z2}
          {One x *S y1 *S z1 +S One x *S y2 *S z2}
          (distlS (One x) (y1 *S z1) (y2 *S z2)) ⟩
    One x *S Row y1 y2 *S Col z1 z2
  ∎

*-assocS .L .L (B s11 s12) (B s21 s22) (One x) (Row y1 y2) (Q z11 z12 z21 z22) =
  *-assoc-lemma1 (One x) y1 z11 y2 z21 ,
  *-assoc-lemma1 (One x) y1 z12 y2 z22
*-assocS .L ._ .L .L (Row x1 x2) (Col y1 y2) (One z) =
  *-assoc-lemma2 x1 y1 x2 y2 (One z)
*-assocS .L ._ .L ._ (Row x1 x2) (Col y1 y2) (Row z1 z2) =
  {!let open EqReasoning setoidS
  in begin
    (x1 *S y1 +S x2 *S y2) *S Row z1 z2
  ≈⟨ ? ⟩
    Row ((x1 *S y1 +S x2 *S y2) *S z1) (x1 *S y1 *S z2 +S x2 *S y2 *S z2)
  ≈⟨ ? ⟩
    ?!}
*-assocS .L ._ ._ .L (Row x1 x2) (Q y11 y12 y21 y22) (Col z1 z2) = {!!}
*-assocS .L ._ ._ ._ (Row x1 x2) (Q y11 y12 y21 y22) (Q z11 z12 z21 z22) = {!!}
*-assocS ._ .L .L .L (Col x1 x2) (One y) (One z) = {!!}
*-assocS ._ .L .L ._ (Col x1 x2) (One y) (Row z1 z2) = {!!}
*-assocS ._ .L ._ .L (Col x1 x2) (Row y1 y2) (Col z1 z2) = {!!}
*-assocS ._ .L ._ ._ (Col x1 x2) (Row y1 y2) (Q z11 z12 z21 z22) = {!!}
*-assocS ._ ._ .L .L (Q x11 x12 x21 x22) (Col y1 y2) (One z) = {!!}
*-assocS ._ ._ .L ._ (Q x11 x12 x21 x22) (Col y1 y2) (Row z1 z2) = {!!}
*-assocS ._ ._ ._ .L (Q x11 x12 x21 x22) (Q y11 y12 y21 y22) (Col z1 z2) = {!!}
*-assocS ._ ._ ._ ._ (Q x11 x12 x21 x22) (Q y11 y12 y21 y22) (Q z11 z12 z21 z22) = {!!}

*-assoc-lemma1 = {!!}
*-assoc-lemma2 = {!!}

Square : Shape → SemiRing
Square shape = record
  { snr = SquareSNR shape
  ; ones = oneS
  ; *-identls = *-identlS
  ; *-identrs = *-identrS
  ; *-assocs  = {!!}
  }

\end{code}
