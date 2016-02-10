\begin{code}

module Product where

open import Level

infixr 4 _,_
infixr 2 _×_


record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B

\end{code}
