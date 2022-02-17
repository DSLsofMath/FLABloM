%if False
\begin{code}
module ClosedSemiRingRecord where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Reasoning.Setoid as EqReasoning
open import Algebra.Definitions using (LeftZero; RightZero)
open import Algebra.Structures using (module IsCommutativeMonoid;
                                             IsCommutativeMonoid)
open import Data.Product
open import Data.Unit

open import Preliminaries

open import SemiNearRingRecord
open import SemiRingRecord
\end{code}
%endif

To define the transitive closure of a semi-ring we extend the Agda
record structure.
%
\savecolumns[CSR]
\begin{code}
record ClosedSemiRing : Set₁ where
  field
    sr : SemiRing

  open SemiRing sr
  open SemiNearRing snr

\end{code}
The defining equation for the closure of a semi-ring is |Eq w c|,
where |c| is the closure of |w|.
%
% We also want to capture that the
% closure of |w| is the least |c| such that |Eq w c| holds this is
% captured by |Closure w c|.
%
\restorecolumns[CSR]
\begin{code}
  Eq : s → s → Set
  Eq w c = c ≃s ones +s w *s c

  Closure : s → s → Set
  Closure w c = Least _≤s_ (Eq w) c
\end{code}
The field |entireQ| captures both the function computing the closure
and that |c| actually is the closure of |w|.
%
\restorecolumns[CSR]
\begin{code}
  field
    entireQ : Entire Eq                           -- |∀ a -> ∃ \ b → R a b|

  closure : s → s
  closure = fun entireQ

  closureHasAll : {w : s} → Eq w (closure w)      -- |w* ≃s ones +s w *s w*|
  closureHasAll = correct entireQ
\end{code}
