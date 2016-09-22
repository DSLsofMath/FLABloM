%if False
\begin{code}
open import SemiNearRingRecord

open import Shape
open import Matrix

open import Algebra.Structures
open import Relation.Binary
open import Product

open import Relation.Binary.PropositionalEquality hiding (trans; sym) renaming (refl to refl-≡)
import Relation.Binary.EqReasoning as EqReasoning
\end{code}

\begin{code}
module LiftSNR (snr : SemiNearRing) where
\end{code}

The Agda module |LiftSNR| is parametrised on the semi-near-ring we
want to lift to the matrix.
%
%if False
\begin{code}
open SemiNearRing snr

S : {r c : Shape} → Set
S {r} {c} = M s r c

infixr 60 _*S_
infixr 50 _+S_
\end{code}
%endif
%
We start by defining matrix addition |+S| (we denote operations lifted
to matrices by a |S| subscript).
%
It is only possible to add matrices of the same size, thus we can
recur on the structure of the matrix and in the case of a 1-by-1
matrix we add the elements using the lifted semi-near-ring addition
operation.
\begin{code}
_+S_ : ∀ {r c} → M s r c → M s r c → M s r c
One x      +S One y      = One  (x +s y)
Row m0 m1  +S Row n0 n1  = Row  (m0 +S n0)  (m1 +S n1)
Col m0 m1  +S Col n0 n1  = Col  (m0 +S n0)  (m1 +S n1)
Q m00 m01 m10 m11 +S Q n00 n01 n10 n11
                         = Q  (m00 +S n00)  (m01 +S n01)
                              (m10 +S n10)  (m11 +S n11)
\end{code}
%
Multiplication is defined similarly: in the 1-by-1 times 1-by-1 case
we use the multiplication from the lifted semi-near-ring and the other
cases follows the simple rule ``row multiplied by column''.
%
Here the structure of the matrix datatype leads to a very intuitive
formulation, and we do not need to fiddle with indices.
%
\begin{code}
_*S_ : ∀ {r m c} → M s r m → M s m c → M s r c
One x      *S One y       = One (x *s y)
One x      *S Row n0 n1   = Row (One x *S n0) (One x *S n1)
Row m0 m1  *S Col n0 n1   = m0 *S n0 +S m1 *S n1
Row m0 m1  *S Q  n00 n01
                 n10 n11  = Row (m0 *S n00 +S m1 *S n10) (m0 *S n01 +S m1 *S n11)
Col m0 m1  *S One x       = Col (m0 *S One x) (m1 *S One x)
Col m0 m1  *S Row n0 n1   = Q  (m0 *S n0)  (m0 *S n1)
                               (m1 *S n0)  (m1 *S n1)
Q  m00 m01
   m10 m11 *S Col n0 n1   = Col  (m00 *S n0 +S m01 *S n1)
                                 (m10 *S n0 +S m11 *S n1)
Q m00 m01 m10 m11 *S Q n00 n01 n10 n11
  = Q  (m00 *S n00 +S m01 *S n10)  (m00 *S n01 +S m01 *S n11)
       (m10 *S n00 +S m11 *S n10)  (m10 *S n01 +S m11 *S n11)
\end{code}

\begin{code}
zerS : (r c : Shape)     → M s r c
zerS L         L         =  One zers
zerS L         (B s s₁)  =  Row  (zerS L s)   (zerS L s₁)
zerS (B r r₁)  L         =  Col  (zerS r L)   (zerS r₁ L)
zerS (B r r₁)  (B s s₁)  =  Q    (zerS r s)   (zerS r s₁)
                                 (zerS r₁ s)  (zerS r₁ s₁)
\end{code}
%endif

To give a taste of the formal development we include one simple proof
and a fragment of the larger development.
%
%if False
The equivalence relation is lifted pointwise and all proofs follow the
same structure:
%
\begin{spec}
_≃S_ : {r c : Shape} → M s r c → M s r c → Set
(One x)     ≃S (One x₁)      =  x ≃s x₁
(Row m m₁)  ≃S (Row n n₁)    =  (m ≃S n) × (m₁ ≃S n₁)
(Col m m₁)  ≃S (Col n n₁)    =  (m ≃S n) × (m₁ ≃S n₁)
(Q m00  m01  m10  m11) ≃S (Q n00  n01  n10  n11)  =
     (m00 ≃S n00) × (m01 ≃S n01) ×
     (m10 ≃S n10) × (m11 ≃S n11)
\end{spec}
%if False
\begin{code}
_≃S_ : {r c : Shape} → M s r c → M s r c → Set
_≃S_ (One x)     (One x₁)    =  x ≃s x₁
_≃S_ (Row m m₁)  (Row n n₁)  =  (m ≃S n) × (m₁ ≃S n₁)
_≃S_ (Col m m₁)  (Col n n₁)  =  (m ≃S n) × (m₁ ≃S n₁)
_≃S_ (Q m00  m01  m10  m11)
     (Q n00  n01  n10  n11)  =  (m00 ≃S n00) × (m01 ≃S n01) ×
                                (m10 ≃S n10) × (m11 ≃S n11)
\end{code}
%endif
\newpage
\noindent
The simplest proof is that of reflexivity:
%
\begin{code}
reflS : {r c : Shape} → (X : M s r c) → X ≃S X
reflS (One x) = refls {x}
reflS (Row X X₁) = reflS X , reflS X₁
reflS (Col X X₁) = reflS X , reflS X₁
reflS (Q X X₁ X₂ X₃) = reflS X , reflS X₁ , reflS X₂ , reflS X₃

symS : {r c : Shape} → (i j : M s r c) → i ≃S j → j ≃S i
symS (One x) (One x₁) p = syms p
symS (Row i i₁) (Row j j₁) (fst , snd) = symS i j fst , symS i₁ j₁ snd
symS (Col i i₁) (Col j j₁) (fst , snd) = symS i j fst , symS i₁ j₁ snd
symS (Q i i₁ i₂ i₃) (Q j j₁ j₂ j₃) (fst , fst₁ , fst₂ , snd)
  = symS i j fst , symS i₁ j₁ fst₁ , symS i₂ j₂ fst₂ , symS i₃ j₃ snd


transS : {r c : Shape} →
  (i j k : M s r c) → i ≃S j → j ≃S k → i ≃S k
transS (One x) (One x₁) (One x₂) p q = trans p q
transS (Row i i₁) (Row j j₁) (Row k k₁) (fst , snd) (fst₁ , snd₁) =
  transS i j k fst fst₁ , transS i₁ j₁ k₁ snd snd₁
transS (Col i i₁) (Col j j₁) (Col k k₁) (fst , snd) (fst₁ , snd₁) =
  transS i j k fst fst₁ , transS i₁ j₁ k₁ snd snd₁
transS (Q i i₁ i₂ i₃) (Q j j₁ j₂ j₃) (Q k k₁ k₂ k₃) (fst , fst₁ , fst₂ , snd) (fst₃ , fst₄ , fst₅ , snd₁) =
  transS i j k fst fst₃ , transS i₁ j₁ k₁ fst₁ fst₄ ,
  transS i₂ j₂ k₂ fst₂ fst₅ , transS i₃ j₃ k₃ snd snd₁

assocS : {r c : Shape} (x y z : M s r c) → ((x +S y) +S z) ≃S (x +S (y +S z))
assocS (One x) (One x₁) (One x₂) = assocs x x₁ x₂
assocS (Row x x₁) (Row y y₁) (Row z z₁) = (assocS x y z) , (assocS x₁ y₁ z₁)
assocS (Col x x₁) (Col y y₁) (Col z z₁) = assocS x y z , assocS x₁ y₁ z₁
assocS (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
  assocS x y z , assocS x₁ y₁ z₁ , assocS x₂ y₂ z₂ , assocS x₃ y₃ z₃

-- assocS L L (One x) (One y) (One z) = assocs x y z
-- assocS L (B c c₁) (Row x x₁) (Row y y₁) (Row z z₁) =
--   assocS L c x y z  , assocS L c₁ x₁ y₁ z₁
-- assocS (B r r₁) L (Col x x₁) (Col y y₁) (Col z z₁) =
--   assocS r L x y z , assocS r₁ L x₁ y₁ z₁
-- assocS (B r r₁) (B c c₁) (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
--   (assocS r c x y z) , (assocS r c₁ x₁ y₁ z₁) ,
--   (assocS r₁ c x₂ y₂ z₂) , (assocS r₁ c₁ x₃ y₃ z₃)

<+S> : {r c : Shape} (x y u v : M s r c) →
  x ≃S y → u ≃S v → (x +S u) ≃S (y +S v)
<+S> (One x) (One x₁) (One x₂) (One x₃) p q = p <+> q
<+S> (Row x x₁) (Row y y₁) (Row u u₁) (Row v v₁) (fst , snd) (fst₁ , snd₁) =
  <+S> x y u v fst fst₁ , <+S> x₁ y₁ u₁ v₁ snd snd₁
<+S> (Col x x₁) (Col y y₁) (Col u u₁) (Col v v₁) p q =
  <+S> x y u v (_×_.fst p) (_×_.fst q) ,
  <+S> x₁ y₁ u₁ v₁ (_×_.snd p) (_×_.snd q)
<+S> (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Q u u₁ u₂ u₃) (Q v v₁ v₂ v₃)
     (fst , fst₁ , fst₂ , snd) (fst₃ , fst₄ , fst₅ , snd₁) =
  <+S> x y u v fst fst₃ , <+S> x₁ y₁ u₁ v₁ fst₁ fst₄ ,
  <+S> x₂ y₂ u₂ v₂ fst₂ fst₅ , <+S> x₃ y₃ u₃ v₃ snd snd₁

-- <+S> L L {One x} {One x₁} {One x₂} {One x₃} p q = p <+> q
-- <+S> L (B c c₁) {Row x x₁} {Row y y₁} {Row u u₁} {Row v v₁} (p , p₁) (q , q₁) =
--   <+S> L c p q , <+S> L c₁ p₁ q₁
-- <+S> (B r r₁) L {Col x x₁} {Col y y₁} {Col u u₁} {Col v v₁} (p , p₁) (q , q₁) =
--   <+S> r L p q , <+S> r₁ L p₁ q₁
-- <+S> (B r r₁) (B c c₁) {Q x x₁ x₂ x₃} {Q y y₁ y₂ y₃} {Q u u₁ u₂ u₃} {Q v v₁ v₂ v₃}
--   (p , p₁ , p₂ , p₃) (q , q₁ , q₂ , q₃) =
--   <+S> r c p q , <+S> r c₁ p₁ q₁ ,
--   <+S> r₁ c p₂ q₂ , <+S> r₁ c₁ p₃ q₃

identlS : {r c : Shape} (x : M s r c) →
   zerS r c +S x ≃S x
identlS (One x) = identityˡs x
identlS (Row x x₁) = identlS x , identlS x₁
identlS (Col x x₁) = identlS x , identlS x₁
identlS (Q x x₁ x₂ x₃) = identlS x , identlS x₁ , identlS x₂ , identlS x₃

-- identSˡ L L (One x) = identityˡs x
-- identSˡ L (B c c₁) (Row x x₁) = identSˡ L c x , identSˡ L c₁ x₁
-- identSˡ (B r r₁) L (Col x x₁) = identSˡ r L x , identSˡ r₁ L x₁
-- identSˡ (B r r₁) (B c c₁) (Q x x₁ x₂ x₃) =
--   identSˡ r c x , identSˡ r c₁ x₁ ,
--   identSˡ r₁ c x₂ , identSˡ r₁ c₁ x₃

commS : {r c : Shape} → (x y : M s r c) →
  (x +S y) ≃S (y +S x)
commS (One x) (One x₁) = comms x x₁
commS (Row x x₁) (Row y y₁) = commS x y , commS x₁ y₁
commS (Col x x₁) (Col y y₁) = commS x y , commS x₁ y₁
commS (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) = commS x y , commS x₁ y₁ , commS x₂ y₂ , commS x₃ y₃

-- commS L L (One x) (One x₁) = comms x x₁
-- commS L (B c c₁) (Row x x₁) (Row y y₁) = (commS L c x y) , (commS L c₁ x₁ y₁)
-- commS (B r r₁) L (Col x x₁) (Col y y₁) = (commS r L x y) , (commS r₁ L x₁ y₁)
-- commS (B r r₁) (B c c₁) (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) =
--   commS r c x y , commS r c₁ x₁ y₁ ,
--   commS r₁ c x₂ y₂ , commS r₁ c₁ x₃ y₃

-- used to make proofs nicer later on
setoidS : {r c : Shape} → Setoid _ _
setoidS {r} {c} =
  record
    { Carrier = M s r c
    ; _≈_ = _≃S_ {r} {c}
    ; isEquivalence =
      record
        { refl = λ {x} → reflS x ; sym = λ {x} {y} → symS x y ; trans = λ {i} {j} {k} → transS i j k } }

\end{code}
%endif
%
The proof examples show how we use the Agda standard library's
equational reasoning framework to make the proofs easier to write and
read, this tool is used heavily throughout the development.
%
To prove that the zero matrix is the right identity of addition we use
commutativity of addition and the proof of the left identity of
addition (which itself is a proof by cases on the shapes of the
matrix):
%\newpage
%
\begin{code}
identrS :  {r c : Shape} (x : M s r c) →
           x +S zerS r c ≃S x
identrS x =
  let open EqReasoning setoidS
  in begin
    x +S zerS _ _
  ≈⟨ commS x (zerS _ _) ⟩
    zerS _ _ +S x
  ≈⟨ identlS x ⟩
    x
  ∎
\end{code}

%if False
\begin{code}
zerolHelp : ∀ r {m m' c : Shape}
  (x : M s m c)
  (y : M s m' c) →
  zerS r m *S x   ≃S  zerS r c  →
  zerS r m' *S y  ≃S  zerS r c  →
  zerS r m *S x +S zerS r m' *S y  ≃S  zerS r c
zerolHelp r {m} {m'} {c} x y p q =
  let open EqReasoning setoidS
  in begin
    zerS r m *S x +S zerS r m' *S y
  ≈⟨ <+S> (zerS r m *S x) (zerS r c) (zerS r m' *S y) (zerS r c) p q ⟩
    zerS r c +S zerS r c
  ≈⟨ identlS (zerS r c) ⟩
    zerS r c
  ∎

zerolS : (a : Shape) {b c : Shape} (x : M s b c) →
  (zerS a b *S x) ≃S zerS a c
zerolS L (One x) = zeroˡ x
zerolS L (Row x x₁) = zerolS L x , zerolS L x₁
zerolS L (Col x x₁) = zerolHelp L x x₁ (zerolS L x) (zerolS L x₁)
zerolS L (Q x x₁ x₂ x₃) =
  zerolHelp L x x₂ (zerolS L x) (zerolS L x₂) ,
  zerolHelp L x₁ x₃ (zerolS L x₁) (zerolS L x₃)
zerolS (B a a₁) (One x) =
  zerolS a (One x) , zerolS a₁ (One x)
zerolS (B a a₁) (Row x x₁) =
  zerolS a x , (zerolS a x₁ ,
  zerolS a₁ x , zerolS a₁ x₁)
zerolS (B a a₁) (Col x x₁) =
  zerolHelp a x x₁ (zerolS a x) (zerolS a x₁) ,
  zerolHelp a₁ x x₁ (zerolS a₁ x) (zerolS a₁ x₁)
zerolS (B a a₁) (Q x x₁ x₂ x₃) =
  zerolHelp a x x₂ (zerolS a x) (zerolS a x₂) ,
  zerolHelp a x₁ x₃ (zerolS a x₁) (zerolS a x₃) ,
  zerolHelp a₁ x x₂ (zerolS a₁ x) (zerolS a₁ x₂) ,
  zerolHelp a₁ x₁ x₃ (zerolS a₁ x₁) (zerolS a₁ x₃)

zerorHelp : ∀ {r m m'} c
  (x : M s r m)
  (x₁ : M s r m') →
  x *S zerS m c ≃S zerS r c →
  x₁ *S zerS m' c ≃S zerS r c →
  x *S zerS m c +S x₁ *S zerS m' c
  ≃S zerS r c
zerorHelp {r} {m} {m'} c x x₁ p q =
  let open EqReasoning setoidS
  in begin
    x *S zerS m c +S x₁ *S zerS m' c
  ≈⟨ <+S> (x *S zerS m c) (zerS r c) (x₁ *S zerS m' c) (zerS r c) p q ⟩
    zerS r c +S zerS r c
  ≈⟨ identlS (zerS r c) ⟩
    zerS r c
  ∎

zerorS : ∀ {a b : Shape} c (x : M s a b) →
  (x *S zerS b c) ≃S zerS a c
zerorS L (One x) = zeroʳ x
zerorS L (Row x x₁) = zerorHelp L x x₁ (zerorS L x) (zerorS L x₁)
zerorS L (Col x x₁) =
  zerorS L x ,
  zerorS L x₁
zerorS L (Q x x₁ x₂ x₃) =
  (zerorHelp L x x₁ (zerorS L x) (zerorS L x₁)) ,
  zerorHelp L x₂ x₃ (zerorS L x₂) (zerorS L x₃)
zerorS (B c c₁) (One x) =
  (zerorS c (One x)) ,
  (zerorS c₁ (One x))
zerorS (B c c₃) (Row x x₁) =
  (zerorHelp c x x₁ (zerorS c x) (zerorS c x₁)) ,
  zerorHelp c₃ x x₁ (zerorS c₃ x) (zerorS c₃ x₁)
zerorS (B c c₁) (Col x x₁) =
  (zerorS c x) ,
  (zerorS c₁ x) ,
  (zerorS c x₁) ,
  (zerorS c₁ x₁)
zerorS (B c c₃) (Q x x₁ x₂ x₃) =
  (zerorHelp c x x₁ (zerorS c x) (zerorS c x₁)) ,
  (zerorHelp c₃ x x₁ (zerorS c₃ x) (zerorS c₃ x₁)) ,
  (zerorHelp c x₂ x₃ (zerorS c x₂) (zerorS _ x₃)) ,
  zerorHelp c₃ x₂ x₃ (zerorS _ x₂) (zerorS _ x₃)

<*S> : ∀ {a b c} (x y : M s a b) (u v : M s b c) →
  x ≃S y → u ≃S v → (x *S u) ≃S (y *S v)
<*S> (One x) (One x₁) (One x₂) (One x₃) p q = p <*> q
<*S> (One x) (One x₁) (Row u u₁) (Row v v₁) p (fst , snd) =
  <*S> (One x) (One x₁) u v p fst ,
  <*S> (One x) (One x₁) u₁ v₁ p snd
<*S> (Row x x₁) (Row y y₁) (Col u u₁) (Col v v₁) (fst , snd) (fst₁ , snd₁) =
  <+S> (x *S u) (y *S v) _ _ (<*S> x y u v fst fst₁) (<*S> x₁ y₁ u₁ v₁ snd snd₁)
<*S> (Row x x₁) (Row y y₁) (Q u u₁ u₂ u₃) (Q v v₁ v₂ v₃) (fst , snd) (fst₁ , fst₂ , fst₃ , snd₂) =
  (<+S> (x *S u) _ _ _ (<*S> x y u v fst fst₁) (<*S> x₁ y₁ u₂ v₂ snd fst₃)) ,
  (<+S> (x *S u₁) _ _ _ (<*S> x y u₁ v₁ fst fst₂) (<*S> x₁ y₁ u₃ v₃ snd snd₂))
<*S> (Col x x₁) (Col y y₁) (One x₂) (One x₃) (fst , snd) q =
  (<*S> x y (One x₂) (One x₃) fst q) ,
  <*S> x₁ y₁ (One x₂) (One x₃) snd q
<*S> (Col x x₁) (Col y y₁) (Row u u₁) (Row v v₁) (fst , snd) (fst₁ , snd₁) =
  <*S> x y u v fst fst₁ ,
  <*S> x y u₁ v₁ fst snd₁ ,
  <*S> x₁ y₁ u v snd fst₁ ,
  <*S> x₁ y₁ u₁ v₁ snd snd₁
<*S> (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Col u u₁) (Col v v₁) (fst , fst₁ , fst₂ , snd) (fst₃ , snd₁) =
  (<+S> (x *S u) _ _ _ (<*S> x y u v fst fst₃) (<*S> x₁ y₁ u₁ v₁ fst₁ snd₁)) ,
  <+S> (x₂ *S u) _ _ _ (<*S> x₂ y₂ u v fst₂ fst₃) (<*S> x₃ y₃ u₁ v₁ snd snd₁)
<*S> (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Q u u₁ u₂ u₃) (Q v v₁ v₂ v₃)
  (fst , fst₁ , fst₂ , snd) (fst₃ , fst₄ , fst₅ , snd₁) =
  (<+S> (x *S u) _ _ _ (<*S> x y u v fst fst₃) (<*S> x₁ y₁ u₂ v₂ fst₁ fst₅)) ,
  <+S> (x *S u₁) _ _ _ (<*S> x y u₁ v₁ fst fst₄) (<*S> x₁ y₁ u₃ v₃ fst₁ snd₁) ,
  (<+S> (x₂ *S u) _ _ _ (<*S> x₂ y₂ u v fst₂ fst₃) (<*S> x₃ y₃ u₂ v₂ snd fst₅)) ,
  (<+S> (x₂ *S u₁) _ _ _ (<*S> x₂ _ _ _ fst₂ fst₄) (<*S> x₃ _ _ _ snd snd₁))

idemS : ∀ {r c} (x : M s r c) → x +S x ≃S x
idemS (One x) = idem x
idemS (Row x x₁) = (idemS x) , (idemS x₁)
idemS (Col x x₁) = (idemS x) , (idemS x₁)
idemS (Q x x₁ x₂ x₃) = idemS x , idemS x₁ , idemS x₂ , idemS x₃

-- swapMid : {r c : Shape} (x y z w : M s r c) →
--   (x +S y) +S (z +S w) ≃S (x +S z) +S (y +S w)
-- swapMid {r} {c} x y z w =
--   let open EqReasoning setoidS
--   in begin
--     {!!}
-- --   -- begin
-- --   --   (x +S y) +S (z +S w)
-- --   -- ≈⟨ assocS _ _ x y (z +S w) ⟩
-- --   --   x +S y +S z +S w
-- --   -- ≈⟨ <+S> r c (reflS r c) (symS r c (assocS r c y z w)) ⟩
-- --   --   x +S (y +S z) +S w
-- --   -- ≈⟨ <+S> r c (reflS r c) (<+S> r c (commS r c y z) (reflS r c)) ⟩
-- --   --   x +S (z +S y) +S w
-- --   -- ≈⟨ <+S> r c (reflS r c) (assocS r c z y w) ⟩
-- --   --   x +S z +S y +S w
-- --   -- ≈⟨ symS r c (assocS r c x z (y +S w)) ⟩
-- --   --   (x +S z) +S (y +S w)
-- --   -- ∎

-- -- distlHelp : ∀ {a b b₁ c₁}
-- --             (x : M s a b)
-- --             (y z : M s b c₁)
-- --             (x₁ : M s a b₁)
-- --             (y₁ z₁ : M s b₁ c₁) →
-- --           (x *S (y +S z)) ≃S (x *S y +S x *S z) →
-- --           (x₁ *S (y₁ +S z₁)) ≃S (x₁ *S y₁ +S x₁ *S z₁) →
-- --           (x *S (y +S z) +S x₁ *S (y₁ +S z₁))
-- --           ≃S ((x *S y +S x₁ *S y₁) +S x *S z +S x₁ *S z₁)
-- -- distlHelp x y z x₁ y₁ z₁ p q =
-- --   let open EqReasoning setoidS
-- --   in begin
-- --     x *S (y +S z) +S x₁ *S (y₁ +S z₁)
-- --   ≈⟨ <+S> _ _ {x *S (y +S z)} {x *S y +S x *S z}
-- --               {x₁ *S (y₁ +S z₁)} {x₁ *S y₁ +S x₁ *S z₁} p q ⟩
-- --     (x *S y +S x *S z) +S x₁ *S y₁ +S x₁ *S z₁
-- --   ≈⟨ swapMid (x *S y) (x *S z) (x₁ *S y₁) (x₁ *S z₁) ⟩
-- --     (x *S y +S x₁ *S y₁) +S x *S z +S x₁ *S z₁
-- --   ∎

-- -- distlS : {a b c : Shape} (x : M s a b) (y z : M s b c) →
-- --   (x *S (y +S z)) ≃S ((x *S y) +S (x *S z))
-- -- distlS {L} {L} {L} (One x) (One y) (One z) = distl x y z
-- -- distlS {L} {L} {B c c₁} (One x) (Row y y₁) (Row z z₁) =
-- --   distlS (One x) y z ,
-- --   distlS (One x) y₁ z₁
-- -- distlS {L} {(B b b₁)} {L} (Row x x₁) (Col y y₁) (Col z z₁) =
-- --   distlHelp x y z x₁ y₁ z₁ (distlS x y z) (distlS x₁ y₁ z₁)
-- -- distlS {L} {(B b b₁)} {(B c c₁)} (Row x x₁) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
-- --   distlHelp x y z x₁ y₂ z₂ (distlS x y z) (distlS x₁ y₂ z₂) ,
-- --   distlHelp x y₁ z₁ x₁ y₃ z₃  (distlS x y₁ z₁) (distlS x₁ y₃ z₃)
-- -- distlS {(B a a₁)} {L} {L} (Col x x₁) (One x₂) (One x₃) =
-- --   distlS x (One x₂) (One x₃) ,
-- --   distlS x₁ (One x₂) (One x₃)
-- -- distlS {(B a a₁)} {L} {(B c c₁)} (Col x x₁) (Row y y₁) (Row z z₁) =
-- --   distlS x y z ,
-- --   distlS x y₁ z₁ ,
-- --   distlS x₁ y z ,
-- --   distlS x₁ y₁ z₁
-- -- distlS {(B a a₁)} {(B b b₁)} {L} (Q x x₁ x₂ x₃) (Col y y₁) (Col z z₁) =
-- --   distlHelp x y z x₁ y₁ z₁ (distlS x y z) (distlS x₁ y₁ z₁) ,
-- --   distlHelp x₂ y z x₃ y₁ z₁ (distlS x₂ y z) (distlS x₃ y₁ z₁)
-- -- distlS {(B a a₁)} {(B b b₁)} {(B c c₁)} (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
-- --   distlHelp x y z x₁ y₂ z₂ (distlS x y z) (distlS x₁ y₂ z₂) ,
-- --   distlHelp x y₁ z₁ x₁ y₃ z₃ (distlS x y₁ z₁) (distlS x₁ y₃ z₃) ,
-- --   distlHelp x₂ y z x₃ y₂ z₂ (distlS x₂ y z) (distlS x₃ y₂ z₂)  ,
-- --   distlHelp x₂ y₁ z₁ x₃ y₃ z₃ (distlS x₂ y₁ z₁) (distlS x₃ y₃ z₃)

-- -- distrHelp : ∀ {r m m₁ c : Shape}
-- --             (x : M s m c)
-- --             (y z : M s r m)
-- --             (x₁ : M s m₁ c)
-- --             (y₁ z₁ : M s r m₁) →
-- --           ((y +S z) *S x) ≃S (y *S x +S z *S x) →
-- --           ((y₁ +S z₁) *S x₁) ≃S (y₁ *S x₁ +S z₁ *S x₁) →
-- --           ((y +S z) *S x +S (y₁ +S z₁) *S x₁)
-- --           ≃S ((y *S x +S y₁ *S x₁) +S z *S x +S z₁ *S x₁)
-- -- distrHelp x y z x₁ y₁ z₁ p q =
-- --   let open EqReasoning setoidS
-- --   in begin
-- --     (y +S z) *S x +S (y₁ +S z₁) *S x₁
-- --   ≈⟨ <+S> _ _ {(y +S z) *S x} {y *S x +S z *S x}
-- --               {(y₁ +S z₁) *S x₁} {y₁ *S x₁ +S z₁ *S x₁} p q ⟩
-- --     (y *S x +S z *S x) +S y₁ *S x₁ +S z₁ *S x₁
-- --   ≈⟨ swapMid (y *S x) (z *S x) (y₁ *S x₁) (z₁ *S x₁) ⟩
-- --     (y *S x +S y₁ *S x₁) +S z *S x +S z₁ *S x₁
-- --   ∎

-- -- distrS : {r m c : Shape} (x : M s m c) (y z : M s r m) →
-- --   ((y +S z) *S x) ≃S ((y *S x) +S (z *S x))
-- -- distrS {L} {L} {L} (One x) (One y) (One z) =
-- --   distr x y z
-- -- distrS {L} {L} {B c c₁} (Row x x₁) (One x₂) (One x₃) =
-- --   (distrS x (One x₂) (One x₃)) ,
-- --   (distrS x₁ (One x₂) (One x₃))
-- -- distrS {L} {B m m₁} {L} (Col x x₁) (Row y y₁) (Row z z₁) =
-- --   distrHelp x y z x₁ y₁ z₁ (distrS x y z) (distrS x₁ y₁ z₁)
-- -- distrS {L} {B m m₁} {B c c₁} (Q x x₁ x₂ x₃) (Row y y₁) (Row z z₁) =
-- --   (distrHelp x y z x₂ y₁ z₁ (distrS x y z) (distrS x₂ y₁ z₁)) ,
-- --   (distrHelp x₁ y z x₃ y₁ z₁ (distrS x₁ y z) (distrS x₃ y₁ z₁))
-- -- distrS {B r r₁} {L} {L} (One x) (Col y y₁) (Col z z₁) =
-- --   distrS (One x) y z ,
-- --   distrS (One x) y₁ z₁
-- -- distrS {B r r₁} {L} {B c c₁} (Row x x₁) (Col y y₁) (Col z z₁) =
-- --   (distrS x y z) ,
-- --   (distrS x₁ y z) ,
-- --   (distrS x y₁ z₁) ,
-- --   (distrS x₁ y₁ z₁)
-- -- distrS {B r r₁} {B m m₁} {L} (Col x x₁) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
-- --   (distrHelp x y z x₁ y₁ z₁ (distrS x y z) (distrS x₁ y₁ z₁)) ,
-- --   (distrHelp x y₂ z₂ x₁ y₃ z₃ (distrS x y₂ z₂) (distrS x₁ y₃ z₃))
-- -- distrS {B r r₁} {B m m₁} {B c c₁} (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
-- --   distrHelp x y z x₂ y₁ z₁ (distrS x y z) (distrS x₂ y₁ z₁) ,
-- --   distrHelp x₁ y z x₃ y₁ z₁ (distrS x₁ y z) (distrS x₃ y₁ z₁) ,
-- --   distrHelp x y₂ z₂ x₂ y₃ z₃ (distrS x y₂ z₂) (distrS x₂ y₃ z₃) ,
-- --   distrHelp x₁ y₂ z₂ x₃ y₃ z₃ (distrS x₁ y₂ z₂) (distrS x₃ y₃ z₃)

-- -- distrS' : {r m c : Shape} (x : M s m c) (y z : M s r m) →
-- --   ((y *S x) +S (z *S x)) ≃S ((y +S z) *S x)
-- -- distrS' {r} {m} {c} x y z = symS r c (distrS x y z)
-- -- \end{code}

-- -- Finally we are able to lift the semi-near-ring to a semi-near-ring of
-- -- matrices (see the module \texttt{LiftSNR} for the full proof), however
-- -- we can only lift to a square matrix (i.e.\ the same shape in both
-- -- dimensions).
-- -- \begin{figure}[h!]
-- -- \begin{multicols}{2}
-- -- \begin{code}
-- -- Square : Shape → SemiNearRing
-- -- Square shape = SNR
-- --   where

-- --   isEquivS =
-- --     record
-- --       { refl   = reflS shape shape
-- --       ; sym    = symS shape shape
-- --       ; trans  = transS shape shape }

-- --   isSemgroupS =
-- --     record
-- --       { isEquivalence  = isEquivS
-- --       ; assoc          = assocS shape shape
-- --       ; ∙-cong         = <+S> shape shape }

-- --   isCommMonS =
-- --     record
-- --       { isSemigroup  = isSemgroupS
-- --       ; identityˡ    = identSˡ shape shape
-- --       ; comm         = commS shape shape }

-- -- \end{code}
-- -- \columnbreak
-- -- \begin{code}

-- --   SNR : SemiNearRing
-- --   SNR =
-- --     record
-- --       { s = S
-- --       ; _≃s_ = _≃S_ {shape} {shape}
-- --       ; zers = zerS shape shape
-- --       ; _+s_ = _+S_
-- --       ; _*s_ = _*S_
-- --       ; isCommMon = isCommMonS
-- --       ; zeroˡ = zeroSˡ shape shape shape
-- --       ; zeroʳ = zeroSʳ shape shape shape
-- --       ; _<*>_ = <*S> shape shape shape
-- --       ; idem = idemS shape shape
-- --       ; distl = distlS {shape} {shape}
-- --       ; distr = distrS {shape} {shape}
-- --       }
-- -- \end{code}
-- -- \end{multicols}
-- -- \caption{Lifting a semi-near-ring to a matrix of square shape.}
-- -- \end{figure}
-- -- %endif
