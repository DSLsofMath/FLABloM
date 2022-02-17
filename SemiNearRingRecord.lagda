%if False
\begin{code}
module SemiNearRingRecord where

import Algebra.Definitions
  using (LeftZero; RightZero; _DistributesOverˡ_;_DistributesOverʳ_; Idempotent)
import Function using (_on_)
import Level
import Relation.Binary.Reasoning.Setoid as EqReasoning
import Relation.Binary.Construct.On using (isEquivalence)
import Algebra.Structures using (module IsCommutativeMonoid; IsCommutativeMonoid)
open import Relation.Binary
  using (module IsEquivalence; IsEquivalence; _Preserves₂_⟶_⟶_ ; Setoid)
open import Data.Product
     using (proj₂)
     renaming (_,_ to _,,_) -- just to avoid clash with other commas

open import Preliminaries
\end{code}
%endif

The weakest structure in this development is a seminearring, we have
defined an Agda record for the operations and properties required of
some type |s| that is a seminearring:
\begin{code}
record SemiNearRing : Set₁ where
\end{code}
A seminearring for a type |s| should have an equivalence relation
|≃s|, a distinguished element of |s|, |zers|, and two binary
operations |+s| and |*s| (addition and multiplication).
%
\savecolumns[SNRR]
\begin{code}
  field
    s : Set
    _≃s_  : s → s → Set
    zers  : s
    _+s_  : s → s → s
    _*s_  : s → s → s

  open Algebra.Structures
    using (IsCommutativeMonoid)
  open Algebra.Definitions _≃s_
    using (LeftZero; RightZero)
\end{code}
A seminearring should be a commutative monoid under addition
(i.e. |+s| commutes and |zers| is the left and right identity of
|+s|).
%
|zers| should also be the left and right absorbing element for |*s|
and we also need that |*s| respects the equivalence relation.
%
\restorecolumns[SNRR]
\begin{code}
  field
    isCommMon  : IsCommutativeMonoid _≃s_ _+s_ zers
    zeroˡ      : LeftZero   zers _*s_
    zeroʳ      : RightZero  zers _*s_
    _<*>_      : ∀ {x y u v} → (x ≃s y) → (u ≃s v) → (x *s u ≃s y *s v)

  infix 4 _≃s_; infixl 6 _+s_; infixl 7 _*s_
\end{code}
%
The semi-rings in this development also have idempotent addition and
|*s| distributes over |+s|.
%
\restorecolumns[SNRR]
\begin{code}
  open Algebra.Definitions _≃s_
    using (Idempotent; _DistributesOverˡ_; _DistributesOverʳ_)

  field
     idem   : Idempotent _+s_
       -- expands to |∀ x → x +s x ≃s x|

     distl  : _*s_ DistributesOverˡ _+s_
     distr  : _*s_ DistributesOverʳ _+s_
       -- expands to |∀ a b c → (a +s b) *s c ≃s (a *s c) +s (b *s c)|
\end{code}
%
Finally we have a definition of inequality for the seminearring.
%
\begin{code}
  infix  4 _≤s_
  _≤s_ : s -> s -> Set
  x ≤s y =  x +s y ≃s y
\end{code}

%if False
\begin{code}

  open Algebra.Structures.IsCommutativeMonoid isCommMon public
    hiding (refl)
    renaming
     (  isEquivalence  to isEquivs
     ;  assoc          to assocs
     ;  comm           to comms
     ;  ∙-cong         to _<+>_
     ;  identityˡ      to identityˡs
     )

  identityʳs = proj₂ identity

  sSetoid : Setoid _ _
  sSetoid = record {  Carrier        = s;
                      _≈_            = _≃s_;
                      isEquivalence  = isEquivs }

  open IsEquivalence isEquivs public
    hiding (reflexive; isPartialEquivalence)
    renaming (refl to refls ; sym to syms ; trans to transs)

  LowerBounds  = LowerBound _≤s_
\end{code}
%endif
