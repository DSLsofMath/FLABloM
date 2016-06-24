%if False
\begin{code}
module Shape where
open import Data.Product
open import Data.Maybe
open import Data.Nat

\end{code}
%endif

To represent the dimensions of matrices we use a type of non-empty
binary trees:
%
\begin{code}
data Shape : Set where
  L  : Shape
  B  : Shape → Shape → Shape
\end{code}
%
This representation follows the structure of the (block) matrix
representation more closely than natural numbers and we can easily
compute the corresponding natural number:
%
\begin{code}
toNat : Shape  →  ℕ
toNat L        =  1
toNat (B l r)  =  toNat l + toNat r
\end{code}
%
while the other direction is slightly more complicated because we want
a somewhat balanced tree and we have no representation for~|0|.

%if False
However there are many representation of a non-zero natural number as
a shape, here we split the number in two almost equal parts to find
a corresponding shape.
\begin{code}
split : ℕ  ->  ℕ × ℕ
split zero        = (zero , zero)
split (suc zero)  = (suc zero , zero)
split (suc (suc n)) with split n
... | (n1 , n2)   = (suc n1 , suc n2)

\end{code}
\begin{code}
{-# TERMINATING #-}
\end{code}

Then a balanced shape is computed, but the function is partial due to
there being no shape corresponding to 0 (this means that we cannot
have degenerate matrices that are 0 in either dimension)
\begin{code}
fromNat : ℕ → Maybe Shape
fromNat zero        = nothing
fromNat (suc zero)  = just L
fromNat n with split n
... | (n1 , n2) with fromNat n1 | fromNat n2
...   | nothing  | nothing  = nothing
...   | just s1  | nothing  = just s1
...   | nothing  | just s2  = just s2
...   | just s1  | just s2  = just (B s1 s2)
\end{code}
%endif
