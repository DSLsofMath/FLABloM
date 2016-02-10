%if False
\begin{code}
open import ClosedSemiRingRecord

module LiftCSR (csr : ClosedSemiRing) where

open import Data.Product renaming (_,_ to _,,_)
open import Product
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality using (refl)

open import Shape
open import Matrix

open import SemiRingRecord
open import SemiNearRingRecord

import LiftSR renaming (Square to SquareSR)

open ClosedSemiRing csr
open SemiRing sr
open SemiNearRing snr

open LiftSR sr
\end{code}
%endif

%PaJa: Nice to see that you found a "summetric" definition instead of Dolan's
%
In \cite{lehmann1977} Lehmann presents a definition of the closure on
square matrices, $A^* = 1 + A · A^*$:
%
Given
%
\[
  A = \left[
  \begin{array}{ll}
    A_{11} & A_{12} \\
    A_{21} & A_{22}
  \end{array}
  \right]
\]
%
the transitive closure of $A$ is defined inductively as
%
\[
  A^* = \left[
  \begin{array}{ll}
    A_{11}^* + A_{11}^* · A_{12} · Δ^* · A_{21} · A_{11}^*
    & A_{11}^* · A_{12} · Δ^* \\
    Δ^* · A_{21} · A_{11}^*
    & Δ^*
  \end{array}
  \right]
\]
%
where $Δ = A_{22} + A_{21} · A_{11}^* · A_{12}$ and the base case
being the one-by-one matrix where we use the transitive closure of the
element of the matrix:
%
\[
\left[ s \right]^* = \left[ s^* \right]
\]

%if False
\begin{code}
EqS : ∀ {sh} → M s sh sh → M s sh sh → Set
EqS w c = oneS +S w *S c ≃S c

-- from Lehmann
lemma2-1-1 :
  ∀ sh sh1
  (M2 : M s sh sh)
  (M1 : M s sh sh1) →
  (oneS +S M2) *S M1 ≃S M1 +S M2 *S M1
lemma2-1-1 sh sh1 M2 M1 =
  let open EqReasoning setoidS
  in begin
    (oneS +S M2) *S M1
  ≈⟨ distrS M1 oneS M2 ⟩
    oneS *S M1 +S M2 *S M1
  ≈⟨ <+S> sh sh1 {oneS *S M1}{M1}{M2 *S M1}{M2 *S M1}
       (*-identlS {sh}{sh1} M1)
       (reflS sh sh1) ⟩
    M1 +S M2 *S M1
  ∎
  -- ≈⟨ <+S> {!sh!} {!!} (*-identlS M1) (reflS sh sh) ⟩
  --   M1 +S M2 *S M1
  -- ∎

-- TODO: rename
lemma2-1-2 : ∀ sh (M1 M2 : M s sh sh) → M1 *S (oneS +S M2) ≃S M1 +S M1 *S M2
lemma2-1-2 sh M1 M2 =
  let open EqReasoning setoidS
  in begin
    M1 *S (oneS +S M2)
  ≈⟨ distlS M1 oneS M2 ⟩
    M1 *S oneS +S M1 *S M2
  ≈⟨ <+S> sh sh (*-identrS M1) (reflS sh sh) ⟩
    M1 +S M1 *S M2
  ∎

entire-lem1 :
  ∀ sh sh1
  (C C* : M s sh sh)
  (D : M s sh sh1) (E : M s sh1 sh)
  (Δ* : M s sh1 sh1)
  (ih : C* ≃S oneS +S C *S C*) →
  C* *S D *S Δ* *S E *S C* ≃S
  C *S C* *S D *S Δ* *S E *S C*  +S  D *S Δ* *S E *S C*
entire-lem1 sh sh1 C C* D E Δ* ih =
  let open EqReasoning setoidS
  in begin
    C* *S D *S Δ* *S E *S C*
  ≈⟨ <*S> sh sh sh {C*}{oneS +S C *S C*}{_}{_}
       ih (reflS sh sh) ⟩
    (oneS +S C *S C*) *S D *S Δ* *S E *S C*
  ≈⟨ distrS (D *S Δ* *S E *S C*) oneS (C *S C*) ⟩
    oneS *S D *S Δ* *S E *S C*
      +S (C *S C*) *S D *S Δ* *S E *S C*
  ≈⟨ <+S> sh sh
          {oneS *S D *S Δ* *S E *S C*}{D *S Δ* *S E *S C*}
          {(C *S C*) *S D *S Δ* *S E *S C*}{C *S C* *S D *S Δ* *S E *S C*}
       (*-identlS (D *S Δ* *S E *S C*))
       (*-assocS sh sh sh sh C C* (D *S Δ* *S E *S C*)) ⟩
    D *S Δ* *S E *S C*
      +S C *S C* *S D *S Δ* *S E *S C*
  ≈⟨ commS sh sh (D *S Δ* *S E *S C*) (C *S C* *S D *S Δ* *S E *S C*) ⟩
    C *S C* *S D *S Δ* *S E *S C*
      +S D *S Δ* *S E *S C*
  ∎

entire-lem2 :
  ∀ sh sh1
  (C C* : M s sh sh)
  (D : M s sh sh1) (E : M s sh1 sh)
  (Δ* : M s sh1 sh1) →
  C *S C*
    +S C *S C* *S D *S Δ* *S E *S C*
    +S D *S Δ* *S E *S C* ≃S
  C *S (C* +S C* *S D *S Δ* *S E *S C*) +S D *S Δ* *S E *S C*
entire-lem2 sh sh1 C C* D E Δ* =
  let open EqReasoning setoidS
  in begin
    C *S C*
    +S C *S C* *S D *S Δ* *S E *S C*
    +S D *S Δ* *S E *S C*
  ≈⟨ symS sh sh {(C *S C*
     +S C *S C* *S D *S Δ* *S E *S C*)
    +S D *S Δ* *S E *S C*}{C *S C*
    +S C *S C* *S D *S Δ* *S E *S C*
    +S D *S Δ* *S E *S C*} (assocS sh sh (C *S C*) (C *S C* *S D *S Δ* *S E *S C*) (D *S Δ* *S E *S C*)) ⟩
    (C *S C*
     +S C *S C* *S D *S Δ* *S E *S C*)
    +S D *S Δ* *S E *S C*
  ≈⟨ <+S> sh sh
          {C *S C* +S C *S C* *S D *S Δ* *S E *S C*}{C *S (C* +S C* *S D *S Δ* *S E *S C*)}
          {D *S Δ* *S E *S C*}{D *S Δ* *S E *S C*}
       (symS sh sh {C *S (C* +S C* *S D *S Δ* *S E *S C*)}
             {(C *S C* +S C *S C* *S D *S Δ* *S E *S C*)}
         (distlS {sh}{sh}{sh}
           C C* (C* *S D *S Δ* *S E *S C*)))
       (reflS sh sh) ⟩
    C *S (C* +S C* *S D *S Δ* *S E *S C*) +S D *S Δ* *S E *S C*
  ∎

entire-lem3 :
  ∀ sh sh1
  (C* : M s sh sh)
  (D : M s sh sh1) (E : M s sh1 sh)
  (F : M s sh1 sh1)
  (Δ* : M s sh1 sh1) →
  let Δ = F +S E *S C* *S D in
  (Δ *S Δ*) *S E *S C* ≃S
  E *S C* *S D *S Δ* *S E *S C*
    +S F            *S Δ* *S E *S C*
entire-lem3 sh1 sh C* D E F Δ* =
  let Δ = F +S E *S C* *S D
  in let open EqReasoning setoidS
  in begin
    (Δ *S Δ*) *S E *S C*
  ≈⟨ *-assocS sh sh sh sh1 Δ Δ* (E *S C*)  ⟩ -- *-assocS
    Δ *S Δ* *S E *S C*
  ≡⟨ refl ⟩ -- def of Δ
    (F +S E *S C* *S D) *S Δ* *S E *S C*
  ≈⟨ (distrS {sh}{sh}{sh1}
       (Δ* *S E *S C*) F (E *S C* *S D)) ⟩ -- <+S> reflS distrS
   F              *S Δ* *S E *S C*
   +S (E *S C* *S D) *S Δ* *S E *S C*
  ≈⟨ (commS sh sh1 (F *S Δ* *S E *S C*) ((E *S C* *S D) *S Δ* *S E *S C*)) ⟩ -- <+S> reflS commS
   (E *S C* *S D) *S Δ* *S E *S C*
   +S F           *S Δ* *S E *S C*
  ≈⟨ <+S> sh sh1 {(E *S C* *S D) *S Δ* *S E *S C*}{((E *S C*) *S D) *S Δ* *S E *S C*}
          {F *S Δ* *S E *S C*}{F *S Δ* *S E *S C*}
       (<*S> sh sh sh1 {(E *S C* *S D)}{(E *S C*) *S D}{Δ* *S E *S C*}{Δ* *S E *S C*}
         (symS sh sh {(E *S C*) *S D}{E *S C* *S D}
           (*-assocS sh sh1 sh1 sh
             E C* D))
         (reflS sh sh1))
       (reflS sh sh1) ⟩ -- (<+S> *-assocS reflS)
    ((E *S C*) *S D) *S Δ* *S E *S C*
    +S F           *S Δ* *S E *S C*
  ≈⟨ <+S> sh sh1 {((E *S C*) *S D) *S Δ* *S E *S C*}{(E *S C*) *S D *S Δ* *S E *S C*}
          {F *S Δ* *S E *S C*}{F *S Δ* *S E *S C*}
       (*-assocS sh sh1 sh sh1
         (E *S C*) D (Δ* *S E *S C*))
       (reflS sh sh1) ⟩ -- (<+S> *-assocS reflS)
    (E *S C*) *S D *S Δ* *S E *S C*
    +S F           *S Δ* *S E *S C*
  ≈⟨ <+S> sh sh1 {(E *S C*) *S D *S Δ* *S E *S C*}{E *S C* *S D *S Δ* *S E *S C*}
          {_}{_}
       (*-assocS sh sh1 sh1 sh1
         E C* (D *S Δ* *S E *S C*))
       (reflS sh sh1) ⟩ -- (<+S> *-assocS reflS)
    E *S C* *S D *S Δ* *S E *S C*
    +S F           *S Δ* *S E *S C*
  ∎


entireQS : ∀ {sh} (c : M s sh sh) → Σ (M s sh sh) λ c* → c* ≃S oneS +S c *S c*
entireQS {L} (One w) =
  let (c ,, p) = entireQ w
  in (One c ,, p)
entireQS {B sh sh1} (Q C D E F) =
  let
    C* ,, ih_C = entireQS C
    Δ = F +S E *S C* *S D
    Δ* ,, ih_Δ = entireQS Δ
  in
    Q (C* +S C* *S D *S Δ* *S E *S C*) (C* *S D *S Δ*)
      (Δ* *S E *S C*) Δ* ,,
    (let open EqReasoning setoidS
    in begin
      C* +S C* *S D *S Δ* *S E *S C*
    ≈⟨ <+S> sh sh
            {C*}{oneS +S C *S C*}{C* *S D *S Δ* *S E *S C*}
            {C *S C* *S D *S Δ* *S E *S C*  +S  D *S Δ* *S E *S C*}
         ih_C
         (entire-lem1 sh sh1 C C* D E Δ* ih_C) ⟩
      (oneS +S C *S C*)
        +S C *S C* *S D *S Δ* *S E *S C* +S D *S Δ* *S E *S C*
    ≈⟨ assocS sh sh oneS (C *S C*) (C *S C* *S D *S Δ* *S E *S C* +S D *S Δ* *S E *S C*)  ⟩
      oneS +S C *S C*
        +S C *S C* *S D *S Δ* *S E *S C* +S D *S Δ* *S E *S C*
    ≈⟨ <+S> sh sh {oneS}{oneS}
            {C *S C* +S C *S C* *S D *S Δ* *S E *S C* +S D *S Δ* *S E *S C*}
            {(C *S (C* +S C* *S D *S Δ* *S E *S C*) +S D *S Δ* *S E *S C*)}
         (reflS sh sh)
         (entire-lem2 sh sh1 C C* D E Δ*) ⟩
      oneS +S C *S (C* +S C* *S D *S Δ* *S E *S C*) +S D *S Δ* *S E *S C*
    ∎) ,
    (let open EqReasoning setoidS
    in begin
      C* *S D *S Δ*
    ≈⟨ <*S> sh sh sh1 {C*}{oneS +S C *S C*}
            {D *S Δ*}{D *S Δ*}
         ih_C (reflS sh sh1) ⟩
      (oneS +S C *S C*) *S D *S Δ*
    ≈⟨ distrS (D *S Δ*) oneS (C *S C*) ⟩
      oneS *S (D *S Δ*) +S (C *S C*) *S (D *S Δ*)
    ≈⟨ <+S> sh sh1 {oneS *S (D *S Δ*)}{D *S Δ*}{_}{_}
         (*-identlS (D *S Δ*))
         (reflS sh sh1) ⟩
      D *S Δ* +S (C *S C*) *S (D *S Δ*)
    ≈⟨ commS sh sh1 (D *S Δ*) ((C *S C*) *S (D *S Δ*)) ⟩
      (C *S C*) *S D *S Δ* +S D *S Δ*
    ≈⟨ <+S> sh sh1 {(C *S C*) *S D *S Δ*}{C *S C* *S D *S Δ*}{_}{_}
         (*-assocS sh sh sh sh1 C C* (D *S Δ*))
         (reflS sh sh1) ⟩
      C *S C* *S D *S Δ* +S D *S Δ*
    ≈⟨ symS sh sh1 {zerS sh sh1 +S C *S C* *S D *S Δ* +S D *S Δ*}
            {C *S C* *S D *S Δ* +S D *S Δ*}
         (identSˡ sh sh1 (C *S C* *S D *S Δ* +S D *S Δ*)) ⟩
      zerS sh sh1 +S C *S C* *S D *S Δ* +S D *S Δ*
    ∎) ,
    (let open EqReasoning setoidS
    in begin
      Δ* *S E *S C*
    ≈⟨ <*S> sh1 sh1 sh {Δ*}{oneS +S Δ *S Δ*}{E *S C*}{E *S C*}
         ih_Δ
         (reflS sh1 sh) ⟩ -- <*S> ih_Δ reflS
      (oneS +S Δ *S Δ*) *S E *S C*
    ≈⟨ lemma2-1-1 sh1 sh (Δ *S Δ*) (E *S C*) ⟩ -- lemma 2.1-1
      E *S C* +S (Δ *S Δ*) *S E *S C*
    ≈⟨ <+S> sh1 sh {E *S C*}{E *S C*}
            {(Δ *S Δ*) *S E *S C*}{E *S C* *S D *S Δ* *S E *S C* +S F *S Δ* *S E *S C*}
         (reflS sh1 sh)
         (entire-lem3 sh sh1 C* D E F Δ*) ⟩
      E *S C*
        +S E *S C* *S D *S Δ* *S E *S C*
        +S F            *S Δ* *S E *S C*
    ≈⟨ symS sh1 sh {(E *S C*
        +S E *S C* *S D *S Δ* *S E *S C*)
        +S F            *S Δ* *S E *S C*}{E *S C*
        +S E *S C* *S D *S Δ* *S E *S C*
        +S F            *S Δ* *S E *S C*}
         (assocS sh1 sh (E *S C*) (E *S C* *S D *S Δ* *S E *S C*) (F *S Δ* *S E *S C*)) ⟩
      (E *S C*
        +S E *S C* *S D *S Δ* *S E *S C*)
        +S F            *S Δ* *S E *S C*
    ≈⟨ <+S> sh1 sh
            {E *S C* +S E *S C* *S D *S Δ* *S E *S C*}{E *S (C* +S C* *S D *S Δ* *S E *S C*)}
            {F *S Δ* *S E *S C*}{F *S Δ* *S E *S C*}
         (symS sh1 sh {E *S (C* +S C* *S D *S Δ* *S E *S C*)}{E *S C* +S E *S C* *S D *S Δ* *S E *S C*}
           (distlS E C* (C* *S D *S Δ* *S E *S C*)))
         (reflS sh1 sh) ⟩ -- <+S> (symS distlS) reflS
      E *S (C* +S C* *S D *S Δ* *S E *S C*)
        +S F *S Δ* *S E *S C*
    ≈⟨ symS sh1 sh {zerS sh1 sh
        +S (E *S (C* +S C* *S D *S Δ* *S E *S C*)
        +S F *S Δ* *S E *S C*)}{E *S (C* +S C* *S D *S Δ* *S E *S C*)
        +S F *S Δ* *S E *S C*}
         (identSˡ sh1 sh (E *S (C* +S C* *S D *S Δ* *S E *S C*) +S F *S Δ* *S E *S C*)) ⟩ -- symS identSˡ
      zerS sh1 sh
        +S E *S (C* +S C* *S D *S Δ* *S E *S C*)
        +S F *S Δ* *S E *S C*
    ∎) ,
    (let open EqReasoning setoidS
    in begin
      Δ*
    ≈⟨ ih_Δ ⟩
      oneS +S Δ *S Δ*
    ≡⟨ refl ⟩
      oneS +S (F +S E *S C* *S D) *S Δ*
    ≈⟨ <+S> sh1 sh1 {oneS}{oneS}{(F +S E *S C* *S D) *S Δ*}{F *S Δ* +S (E *S C* *S D) *S Δ*}
         (reflS sh1 sh1)
         (distrS Δ* F (E *S C* *S D)) ⟩
      oneS +S F *S Δ* +S (E *S C* *S D) *S Δ*
    ≈⟨ <+S> sh1 sh1 {_}{_}{F *S Δ* +S (E *S C* *S D) *S Δ*}{(E *S C* *S D) *S Δ* +S F *S Δ*}
         (reflS sh1 sh1)
         (commS sh1 sh1 (F *S Δ*) ((E *S C* *S D) *S Δ*)) ⟩
      oneS +S (E *S C* *S D) *S Δ* +S F *S Δ*
    ≈⟨ <+S> sh1 sh1 {oneS}{oneS}
            {(E *S C* *S D) *S Δ* +S F *S Δ*}{E *S (C* *S D) *S Δ* +S F *S Δ*}
         (reflS sh1 sh1)
         (<+S> sh1 sh1 {(E *S C* *S D) *S Δ*}{E *S (C* *S D) *S Δ*}
               {F *S Δ*}{F *S Δ*}
           (*-assocS sh1 sh sh1 sh1 E (C* *S D) Δ*)
           (reflS sh1 sh1)) ⟩
      oneS +S E *S (C* *S D) *S Δ* +S F *S Δ*
    ≈⟨ <+S> sh1 sh1 {oneS}{oneS}{E *S (C* *S D) *S Δ* +S F *S Δ*}{E *S C* *S D *S Δ* +S F *S Δ*}
         (reflS sh1 sh1)
         (<+S> sh1 sh1 {E *S (C* *S D) *S Δ*}{E *S C* *S D *S Δ*}{F *S Δ*}{F *S Δ*}
           (<*S> sh1 sh sh1 {E}{E}{(C* *S D) *S Δ*}{C* *S D *S Δ*}
             (reflS sh1 sh)
             (*-assocS sh sh sh1 sh1 C* D Δ*))
           (reflS sh1 sh1)) ⟩
      oneS +S E *S C* *S D *S Δ* +S F *S Δ*
    ∎)



Square : Shape → ClosedSemiRing
Square shape =
  record
    { sr = SquareSR shape
    ; entireQ = entireQS }


\end{code}
%endif
