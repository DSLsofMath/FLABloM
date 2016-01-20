%if False
\begin{code}
open import ClosedSemiRingRecord

module LiftCSR (csr : ClosedSemiRing) where

open import Data.Product
import Relation.Binary.EqReasoning as EqReasoning


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
matrices, $A^* = 1 + A · A^*$.
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
the transitive closure of $A$ is recursively defined as
%**TODO "recursively defined" := "defined inductively"?
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
being the one-by-one matrix case where we use the transitive closure
of the element of the matrix:
%
\[
\left[ s \right]^* = \left[ s^* \right]
\]

%if False
\begin{code}
EqS : ∀ {sh} → M s sh sh → M s sh sh → Set
EqS w c = oneS +S w *S c ≃S c

-- from Lehmann
lemma2-1-1 : ∀ sh (M1 M2 : M s sh sh) → (oneS +S M2) *S M1 ≃S M1 +S M2 *S M1
lemma2-1-1 sh M1 M2 =
  let open EqReasoning setoidS
  in begin
    (oneS +S M2) *S M1
  ≈⟨ distrS M1 oneS M2 ⟩
    oneS *S M1 +S M2 *S M1
  ≈⟨ <+S> sh sh (*-identlS M1) (reflS sh sh) ⟩
    M1 +S M2 *S M1
  ∎

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

entireQS : ∀ {sh} (w : M s sh sh) → Σ (M s sh sh) λ c → c ≃S oneS +S w *S c --EqS w c
entireQS {L} (One w) =
  let (c , p) = entireQ w
  in (One c , p)
entireQS {B sh sh₁} (Q C D E F) =
  let
    C* , ih_C = entireQS C
    Δ = F +S E *S C* *S D
    Δ* , ih_Δ = entireQS Δ
  in
    Q (C* +S C* *S D *S Δ* *S E *S C*) (C* *S D *S Δ*)
      (Δ* *S E *S C*) Δ* ,
    (let open EqReasoning setoidS
    in begin
      C* +S C* *S D *S Δ* *S E *S C*

    ≈⟨ <+S> sh sh ih_C (reflS sh sh) ⟩

      (oneS +S C *S C*) +S C* *S D *S Δ* *S E *S C*

    ≈⟨ <+S> sh sh (reflS sh sh) (<*S> sh sh sh ih_C (reflS sh sh)) ⟩

      (oneS +S C *S C*) +S (oneS +S C *S C*) *S (D *S Δ* *S E *S C*)

    ≈⟨ <+S> sh sh (reflS sh sh) (lemma2-1-1 sh (D *S Δ* *S E *S C*) (C *S C*)) ⟩

      (oneS +S C *S C*) +S (D *S Δ* *S E *S C*) +S (C *S C*) *S D *S Δ* *S E *S C*

    ≈⟨ {!!} ⟩
      {!!}
    ) ,
    {!!} ,
    {!!} ,
    {!!}

-- Square : Shape → ClosedSemiRing
-- Square shape =
--   record
--     { sr = SquareSR shape
--     ; entireQ = entireQS }


\end{code}
%endif
