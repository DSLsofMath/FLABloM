\begin{code}
open import SemiRingRecord

module LiftSR (sr : SemiRing) where

open import Shape
open import Matrix

open import Algebra.Structures
open import Relation.Binary
open import Product
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using () renaming (refl to ≡-refl)


open import SemiNearRingRecord

open SemiRing sr
open SemiNearRing snr

open import LiftSNR snr renaming (Square to SquareSNR) public


lemma-row : ∀ {c1 c2} (x y : M s L c1) (u v : M s L c2) →
  x ≃S y → u ≃S v →
  Row x u ≃S Row y v
lemma-row (One x) (One x₁) (One x₂) (One x₃) p q = p , q
lemma-row (One x) (One x₁) (Row u₁ u) (Row v v₁) p q = p , q
lemma-row (Row x x₁) (Row y y₁) (One x₂) (One x₃) p q = p , q
lemma-row (Row x x₁) (Row y y₁) (Row u₁ u) (Row v v₁) p q = p , q


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

-- assoc-lem1 : ∀ →
assoc-lem1 : ∀
  sh1 sh2 sh3 sh4 sh5 sh6
  (x : M s sh1 sh2)
  (x₁ : M s sh1 sh3)
  (y : M s sh2 sh4)
  (y₁ : M s sh2 sh5)
  (y₂ : M s sh3 sh4)
  (y₃ : M s sh3 sh5)
  (z : M s sh4 sh6)
  (z₁ : M s sh5 sh6) →
  (x *S y +S x₁ *S y₂) *S z +S (x *S y₁ +S x₁ *S y₃) *S z₁ ≃S
  x *S (y *S z +S y₁ *S z₁) +S x₁ *S (y₂ *S z +S y₃ *S z₁)



assoc-lem2 : ∀ sh sh2 (x : M s L L) (y : M s L sh) (y₁ : M s L sh2) → x *S Row y y₁ ≃S  Row (x *S y) (x *S y₁)
assoc-lem2 sh sh2 (One x) y y₁ = (reflS L sh) , (reflS L sh2)
-- One x *S y ≃S One x *S y × One x *S y₁ ≃S One x *S y₁

assoc-lem3 : ∀ sh1 sh2
  (x : M s sh1 L)
  (x₁ : M s sh2 L)
  (y : M s L L) →
  Col (x *S y) (x₁ *S y) ≃S Col x x₁ *S y
assoc-lem3 L L (One x) (One x₁) (One x₂) = refls , refls
assoc-lem3 L (B sh2 sh3) (One x) (Col x₁ x₂) (One x₃) =
  refls ,
  reflS sh2 L {x₁ *S One x₃} ,
  reflS sh3 L {x₂ *S One x₃}
assoc-lem3 (B sh1 sh2) L (Col x x₁) (One x₂) (One x₃) =
  ((reflS sh1 L {x *S One x₃}) ,
  (reflS sh2 L {x₁ *S One x₃})) ,
  refls
assoc-lem3 (B sh1 sh2) (B sh3 sh4) (Col x x₁) (Col x₂ x₃) (One x₄) =
  ((reflS sh1 L {x *S One x₄}) ,
  (reflS sh2 L {x₁ *S One x₄})) ,
  ((reflS sh3 L {x₂ *S One x₄}) ,
  (reflS sh4 L {x₃ *S One x₄}))

assoc-lem4 : ∀
  sh1 sh3 sh4 sh6
  (x : M s sh1 L)
  (y : M s L sh3)
  (z : M s sh3 sh6)
  (y₁ : M s L sh4)
  (z₁ : M s sh4 sh6) →
  (x *S y) *S z +S (x *S y₁) *S z₁ ≃S
  x *S (y *S z +S y₁ *S z₁)

-- distrS then IH
assoc-lem5 :
  ∀ sh1 sh3 sh4 sh5
  (x : M s sh1 sh3)
  (y : M s sh3 L)
  (x₁ : M s sh1 sh4)
  (y₁ : M s sh4 L)
  (z : M s L sh5) →
  (x *S y +S x₁ *S y₁) *S z ≃S
  x *S y *S z +S x₁ *S y₁ *S z


*-assocS : ∀ sh1 sh2 sh3 sh4 (x : M s sh1 sh2) (y : M s sh2 sh3) (z : M s sh3 sh4)
  → ((x *S y) *S z) ≃S x *S y *S z

*-assocS L L L L (One x) (One x₁) (One x₂) = *-assocs x x₁ x₂

*-assocS L L L (B sh4 sh5) (One x) (One x₁) (Row z z₁) =
  *-assocS L L L sh4 (One x) (One x₁) z ,
  *-assocS L L L sh5 (One x) (One x₁) z₁

*-assocS L L (B sh3 sh4) L (One x) (Row y y₁) (Col z z₁) =
  let open EqReasoning setoidS
  in begin
    (One x *S y) *S z +S (One x *S y₁) *S z₁
  ≈⟨ <+S> L L {(One x *S y) *S z}{One x *S (y *S z)}{(One x *S y₁) *S z₁}{One x *S (y₁ *S z₁)}
       (*-assocS L L sh3 L (One x) y z)
       (*-assocS L L sh4 L (One x) y₁ z₁) ⟩
    One x *S (y *S z) +S One x *S (y₁ *S z₁)
  ≈⟨ symS L L {One x *S (y *S z +S y₁ *S z₁)}{One x *S (y *S z) +S One x *S (y₁ *S z₁)}
          (distlS {L}{L}{L}
            (One x) (y *S z) (y₁ *S z₁)) ⟩
    One x *S (y *S z +S y₁ *S z₁)
  ∎

*-assocS L L (B sh3 sh4) (B sh5 sh6) (One x) (Row y y₁) (Q z z₁ z₂ z₃) =
  (let open EqReasoning setoidS
  in begin
    (One x *S y) *S z +S (One x *S y₁) *S z₂
  ≈⟨ <+S> L sh5 {(One x *S y) *S z}{One x *S y *S z}{(One x *S y₁) *S z₂}{One x *S y₁ *S z₂}
       (*-assocS L L sh3 sh5 (One x) y z)
       (*-assocS L L sh4 sh5 (One x) y₁ z₂) ⟩
    One x *S y *S z +S One x *S y₁ *S z₂
  ≈⟨ symS L sh5 {One x *S (y *S z +S y₁ *S z₂)}{One x *S y *S z +S One x *S y₁ *S z₂}
       (distlS {L}{L}{sh5}
         (One x) (y *S z) (y₁ *S z₂)) ⟩
    One x *S (y *S z +S y₁ *S z₂)
  ∎) ,
    -- (One x *S y) *S z +S (One x *S y₁) *S z₂ ≃S
    -- One x *S (y *S z +S y₁ *S z₂)
  (let open EqReasoning setoidS
  in begin
    (One x *S y) *S z₁ +S (One x *S y₁) *S z₃
  ≈⟨ <+S> L sh6 {(One x *S y) *S z₁}{One x *S y *S z₁}{(One x *S y₁) *S z₃}{One x *S y₁ *S z₃}
       (*-assocS L L sh3 sh6 (One x) y z₁)
       (*-assocS L L sh4 sh6 (One x) y₁ z₃) ⟩
    One x *S y *S z₁ +S One x *S y₁ *S z₃
  ≈⟨ symS L sh6 {One x *S (y *S z₁ +S y₁ *S z₃)}{One x *S y *S z₁ +S One x *S y₁ *S z₃}
       (distlS {L}{L}{sh6}
         (One x) (y *S z₁) (y₁ *S z₃)) ⟩
    One x *S (y *S z₁ +S y₁ *S z₃)
  ∎)

-- (One x *S y) *S z₁ +S (One x *S y₁) *S z₃ ≃S
-- One x *S (y *S z₁ +S y₁ *S z₃)

*-assocS L (B sh2 sh3) L L (Row x x₁) (Col y y₁) (One x₂) =
  let open EqReasoning setoidS
  in begin
    (x *S y +S x₁ *S y₁) *S One x₂
  ≈⟨ distrS {L}{L}{L}
       (One x₂) (x *S y) (x₁ *S y₁) ⟩
    (x *S y) *S One x₂ +S (x₁ *S y₁) *S One x₂
  ≈⟨ <+S> L L {(x *S y) *S One x₂}{x *S y *S One x₂}{(x₁ *S y₁) *S One x₂}{x₁ *S y₁ *S One x₂}
       (*-assocS L sh2 L L x y (One x₂))
       (*-assocS L sh3 L L x₁ y₁ (One x₂)) ⟩
    x *S y *S One x₂ +S x₁ *S y₁ *S One x₂
  ∎
-- (x *S y +S x₁ *S y₁) *S One x₂ ≃S
--       x *S y *S One x₂ +S x₁ *S y₁ *S One x₂

*-assocS L (B sh2 sh3) L (B sh4 sh5) (Row x x₁) (Col y y₁) (Row z z₁) =
  let open EqReasoning setoidS
  in begin
    (x *S y +S x₁ *S y₁) *S Row z z₁
  ≈⟨ distrS {L}{L}{B sh4 sh5} (Row z z₁) (x *S y) (x₁ *S y₁) ⟩
    (x *S y) *S Row z z₁ +S (x₁ *S y₁) *S Row z z₁
  ≈⟨ <+S> L (B sh4 sh5) {(x *S y) *S Row z z₁}{Row ((x *S y) *S z) ((x *S y) *S z₁)}
          {(x₁ *S y₁) *S Row z z₁}{Row ((x₁ *S y₁) *S z) ((x₁ *S y₁) *S z₁)}
       (assoc-lem2 sh4 sh5 (x *S y) z z₁)
       (assoc-lem2 sh4 sh5 (x₁ *S y₁) z z₁) ⟩
    Row ((x *S y) *S z) ((x *S y) *S z₁) +S
    Row ((x₁ *S y₁) *S z) ((x₁ *S y₁) *S z₁)
  ≈⟨ <+S> L (B sh4 sh5) {Row ((x *S y) *S z) ((x *S y) *S z₁)}{Row (x *S y *S z) (x *S y *S z₁)}
          {Row ((x₁ *S y₁) *S z) ((x₁ *S y₁) *S z₁)}{Row (x₁ *S y₁ *S z) (x₁ *S y₁ *S z₁)}
       (*-assocS L sh2 L sh4 x y z , *-assocS L sh2 L sh5 x y z₁)
       (*-assocS L sh3 L sh4 x₁ y₁ z , *-assocS L sh3 L sh5 x₁ y₁ z₁) ⟩
    Row (x *S y *S z) (x *S y *S z₁) +S
    Row (x₁ *S y₁ *S z) (x₁ *S y₁ *S z₁)
  ∎

-- (x *S y +S x₁ *S y₁) *S Row z z₁ ≃S
--       Row (x *S y *S z +S x₁ *S y₁ *S z) (x *S y *S z₁ +S x₁ *S y₁ *S z₁)

*-assocS L (B sh2 sh3) (B sh4 sh5) L (Row x x₁) (Q y y₁ y₂ y₃) (Col z z₁) =
  assoc-lem1 L sh2 sh3 sh4 sh5 L x x₁ y y₁ y₂ y₃ z z₁

*-assocS L (B sh2 sh3) (B sh4 sh5) (B sh6 sh7) (Row x x₁) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
  assoc-lem1 L sh2 sh3 sh4 sh5 sh6 x x₁ y y₁ y₂ y₃ z z₂ ,
  assoc-lem1 L sh2 sh3 sh4 sh5 sh7 x x₁ y y₁ y₂ y₃ z₁ z₃


*-assocS (B sh1 sh2) L L L (Col x x₁) (One x₂) (One x₃) =
  *-assocS sh1 L L L x (One x₂) (One x₃) ,
  *-assocS sh2 L L L x₁ (One x₂) (One x₃)

*-assocS (B sh1 sh2) L L (B sh4 sh5) (Col x x₁) (One x₂) (Row z z₁) =
  *-assocS sh1 L L sh4 x (One x₂) z ,
  *-assocS sh1 L L sh5 x (One x₂) z₁ ,
  *-assocS sh2 L L sh4 x₁ (One x₂) z ,
  *-assocS sh2 L L sh5 x₁ (One x₂) z₁

*-assocS (B sh1 sh2) L (B sh3 sh4) L (Col x x₁) (Row y y₁) (Col z z₁) =
  let open EqReasoning setoidS
  in begin
    Col ((x *S y) *S z +S (x *S y₁) *S z₁)
        ((x₁ *S y) *S z +S (x₁ *S y₁) *S z₁)
  ≈⟨ <+S> sh1 L {(x *S y) *S z}{x *S y *S z}{(x *S y₁) *S z₁}{x *S y₁ *S z₁}
       (*-assocS sh1 L sh3 L x y z)
       (*-assocS sh1 L sh4 L x y₁ z₁) ,
     <+S> sh2 L {(x₁ *S y) *S z}{x₁ *S y *S z}{(x₁ *S y₁) *S z₁}{x₁ *S y₁ *S z₁}
       (*-assocS sh2 L sh3 L x₁ y z)
       (*-assocS sh2 L sh4 L x₁ y₁ z₁) ⟩
    Col (x *S y *S z +S x *S y₁ *S z₁)
        (x₁ *S y *S z +S x₁ *S y₁ *S z₁)
  ≈⟨ symS sh1 L {x *S (y *S z +S y₁ *S z₁)}{x *S y *S z +S x *S y₁ *S z₁}
       (distlS {sh1}{L}{L} x (y *S z) (y₁ *S z₁)) ,
     symS sh2 L {x₁ *S (y *S z +S y₁ *S z₁)}{x₁ *S y *S z +S x₁ *S y₁ *S z₁}
       (distlS {sh2}{L}{L} x₁ (y *S z) (y₁ *S z₁)) ⟩
    Col (x *S (y *S z +S y₁ *S z₁))
        (x₁ *S (y *S z +S y₁ *S z₁))
  ≈⟨ assoc-lem3 sh1 sh2 x x₁ ((y *S z +S y₁ *S z₁)) ⟩
    Col x x₁ *S (y *S z +S y₁ *S z₁)
  ∎

*-assocS (B sh1 sh2) L (B sh3 sh4) (B sh5 sh6) (Col x x₁) (Row y y₁) (Q z z₁ z₂ z₃) =
  assoc-lem4 sh1 sh3 sh4 sh5 x y z y₁ z₂ ,
  assoc-lem4 sh1 sh3 sh4 sh6 x y z₁ y₁ z₃ ,
  assoc-lem4 sh2 sh3 sh4 sh5 x₁ y z y₁ z₂ ,
  assoc-lem4 sh2 sh3 sh4 sh6 x₁ y z₁ y₁ z₃

*-assocS (B sh1 sh2) (B sh3 sh4) L L (Q x x₁ x₂ x₃) (Col y y₁) (One x₄) =
  assoc-lem5 sh1 sh3 sh4 L x y x₁ y₁ (One x₄) ,
  assoc-lem5 sh2 sh3 sh4 L x₂ y x₃ y₁ (One x₄)

*-assocS (B sh1 sh2) (B sh3 sh4) L (B sh5 sh6) (Q x x₁ x₂ x₃) (Col y y₁) (Row z z₁) =
  assoc-lem5 sh1 sh3 sh4 sh5 x y x₁ y₁ z ,
  assoc-lem5 sh1 sh3 sh4 sh6 x y x₁ y₁ z₁ ,
  assoc-lem5 sh2 sh3 sh4 sh5 x₂ y x₃ y₁ z ,
  assoc-lem5 sh2 sh3 sh4 sh6 x₂ y x₃ y₁ z₁

*-assocS (B sh1 sh2) (B sh3 sh4) (B sh5 sh6) L (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Col z z₁) =
  assoc-lem1 sh1 sh3 sh4 sh5 sh6 L x x₁ y y₁ y₂ y₃ z z₁ ,
  assoc-lem1 sh2 sh3 sh4 sh5 sh6 L x₂ x₃ y y₁ y₂ y₃ z z₁

*-assocS (B sh1 sh2) (B sh3 sh4) (B sh5 sh6) (B sh7 sh8) (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
  (assoc-lem1 sh1 sh3 sh4 sh5 sh6 sh7 x x₁ y y₁ y₂ y₃ z z₂) ,
  assoc-lem1 sh1 sh3 sh4 sh5 sh6 sh8 x x₁ y y₁ y₂ y₃ z₁ z₃ ,
  assoc-lem1 sh2 sh3 sh4 sh5 sh6 sh7 x₂ x₃ y y₁ y₂ y₃ z z₂ ,
  assoc-lem1 sh2 sh3 sh4 sh5 sh6 sh8 x₂ x₃ y y₁ y₂ y₃ z₁ z₃

assoc-lem1 sh1 sh2 sh3 sh4 sh5 sh6
  x x₁ y y₁ y₂ y₃ z z₁ =
  let open EqReasoning setoidS
  in begin
    (x *S y +S x₁ *S y₂) *S z +S (x *S y₁ +S x₁ *S y₃) *S z₁
  ≈⟨ <+S> sh1 sh6 {(x *S y +S x₁ *S y₂) *S z}{((x *S y) *S z +S (x₁ *S y₂) *S z)}
          {(x *S y₁ +S x₁ *S y₃) *S z₁}{((x *S y₁) *S z₁ +S (x₁ *S y₃) *S z₁)}
       (distrS {sh1}{sh4}{sh6} z (x *S y) (x₁ *S y₂))
       (distrS {sh1}{sh5}{sh6} z₁ (x *S y₁) (x₁ *S y₃)) ⟩
    ((x *S y) *S z +S (x₁ *S y₂) *S z) +S ((x *S y₁) *S z₁ +S (x₁ *S y₃) *S z₁)
  ≈⟨ <+S> sh1 sh6 {((x *S y) *S z +S (x₁ *S y₂) *S z)}{(x *S y *S z +S x₁ *S y₂ *S z)}
          {((x *S y₁) *S z₁ +S (x₁ *S y₃) *S z₁)}{(x *S y₁ *S z₁ +S x₁ *S y₃ *S z₁)}
       (<+S> sh1 sh6 {(x *S y) *S z}{x *S y *S z}{(x₁ *S y₂) *S z}{x₁ *S y₂ *S z}
         (*-assocS sh1 sh2 sh4 sh6 x y z)
         (*-assocS sh1 sh3 sh4 sh6 x₁ y₂ z))
       (<+S> sh1 sh6 {(x *S y₁) *S z₁}{x *S y₁ *S z₁}{(x₁ *S y₃) *S z₁}{x₁ *S y₃ *S z₁}
         (*-assocS sh1 sh2 sh5 sh6 x y₁ z₁)
         (*-assocS sh1 sh3 sh5 sh6 x₁ y₃ z₁)) ⟩
    (x *S y *S z +S x₁ *S y₂ *S z) +S (x *S y₁ *S z₁ +S x₁ *S y₃ *S z₁)
  ≈⟨ swapMid {sh1}{sh6} (x *S y *S z) (x₁ *S y₂ *S z) (x *S y₁ *S z₁) (x₁ *S y₃ *S z₁) ⟩
    (x *S y *S z +S x *S y₁ *S z₁) +S (x₁ *S y₂ *S z +S x₁ *S y₃ *S z₁)
  ≈⟨ <+S> sh1 sh6 {(x *S y *S z +S x *S y₁ *S z₁)}{x *S (y *S z +S y₁ *S z₁)}
          {x₁ *S y₂ *S z +S x₁ *S y₃ *S z₁}{x₁ *S (y₂ *S z +S y₃ *S z₁)}
       (symS sh1 sh6 {x *S (y *S z +S y₁ *S z₁)}{x *S y *S z +S x *S y₁ *S z₁}
         (distlS x (y *S z) (y₁ *S z₁)))
       (symS sh1 sh6 {x₁ *S (y₂ *S z +S y₃ *S z₁)}{x₁ *S y₂ *S z +S x₁ *S y₃ *S z₁}
         (distlS x₁ (y₂ *S z) (y₃ *S z₁))) ⟩
    x *S (y *S z +S y₁ *S z₁) +S x₁ *S (y₂ *S z +S y₃ *S z₁)
  ∎

assoc-lem4 sh1 sh2 sh3 sh4 x y z y₁ z₁ =
  let open EqReasoning setoidS
  in begin
    (x *S y) *S z +S (x *S y₁) *S z₁
  ≈⟨ <+S> sh1 sh4  {(x *S y) *S z}{x *S y *S z}
          {(x *S y₁) *S z₁}{x *S y₁ *S z₁}
       (*-assocS sh1 L sh2 sh4 x y z)
       (*-assocS sh1 L sh3 sh4 x y₁ z₁) ⟩
    x *S y *S z +S x *S y₁ *S z₁
  ≈⟨ symS sh1 sh4 {x *S (y *S z +S y₁ *S z₁)}{x *S y *S z +S x *S y₁ *S z₁}
    (distlS {sh1}{L}{sh4} x (y *S z) (y₁ *S z₁)) ⟩
    x *S (y *S z +S y₁ *S z₁)
  ∎

assoc-lem5 sh1 sh2 sh3 sh5 x y x₁ y₁ z =
  let open EqReasoning setoidS
  in begin
    (x *S y +S x₁ *S y₁) *S z
  ≈⟨ distrS z (x *S y) (x₁ *S y₁) ⟩
    (x *S y) *S z +S (x₁ *S y₁) *S z
  ≈⟨ <+S> sh1 sh5 {(x *S y) *S z}{x *S y *S z}{(x₁ *S y₁) *S z}{x₁ *S y₁ *S z}
       (*-assocS sh1 sh2 L sh5 x y z)
       (*-assocS sh1 sh3 L sh5 x₁ y₁ z) ⟩
    x *S y *S z +S x₁ *S y₁ *S z
  ∎


Square : Shape → SemiRing
Square shape = record
  { snr = SquareSNR shape
  ; ones = oneS
  ; *-identls = *-identlS
  ; *-identrs = *-identrS
  ; *-assocs  = *-assocS shape shape shape shape
  }

\end{code}
