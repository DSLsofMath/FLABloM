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
_≃S_ {L}          {L}          (One x)     (One x₁)    =  x ≃s x₁
_≃S_ {L}          {(B c₁ c₂)}  (Row m m₁)  (Row n n₁)  =  (m ≃S n) × (m₁ ≃S n₁)
_≃S_ {(B r₁ r₂)}  {L}          (Col m m₁)  (Col n n₁)  =  (m ≃S n) × (m₁ ≃S n₁)
_≃S_ {(B r₁ r₂)}  {(B c₁ c₂)}  (Q m00  m01  m10  m11)
                               (Q n00  n01  n10  n11)  =  (m00 ≃S n00) × (m01 ≃S n01) ×
                                                          (m10 ≃S n10) × (m11 ≃S n11)
\end{code}
%endif
\newpage
\noindent
The simplest proof is that of reflexivity:
%
\begin{spec}
reflS : (r c : Shape) →     {X : M s r c}  →  X ≃S X
reflS L          L          {One x} =  refls {x}
reflS L          (B c₁ c₂)  =  reflS L c₁   , reflS L c₂
reflS (B r₁ r₂)  L          =  reflS r₁ L   , reflS r₂ L
reflS (B r₁ r₂)  (B c₁ c₂)  =  reflS r₁ c₁  , reflS r₁ c₂ ,
                               reflS r₂ c₁  , reflS r₂ c₂
\end{spec}
%if False
\begin{code}
reflS : (r c : Shape) →     {X : M s r c}  →  X ≃S X
reflS L          L          {One x}        =  refls {x}
reflS L          (B c₁ c₂)  {Row X Y}      =  reflS L c₁   , reflS L c₂
reflS (B r₁ r₂)  L          {Col X Y}      =  reflS r₁ L   , reflS r₂ L
reflS (B r₁ r₂)  (B c₁ c₂)  {Q X Y Z W}    =  reflS r₁ c₁  , reflS r₁ c₂ ,
                                              reflS r₂ c₁  , reflS r₂ c₂
\end{code}
%endif
\begin{code}
symS : (r c : Shape) → {i j : M s r c} → i ≃S j → j ≃S i
symS L L {One x} {One x₁} p = syms p
symS L (B c₁ c₂) {Row i₁ i₂} {Row j₁ j₂} (p , q) = symS L c₁ p , symS L c₂ q
symS (B r₁ r₂) L {Col i₁ i} {Col j j₁} (p , q) = symS r₁ L p , symS r₂ L q
symS (B r r₂) (B c₁ c₂) {Q i₂ i i₃ i₁} {Q j j₁ j₂ j₃} (p , q , x , y) =
  symS r c₁ p , symS r c₂ q ,
  symS r₂ c₁ x , symS r₂ c₂ y

transS : (r c : Shape) →
  {i j k : M s r c} → i ≃S j → j ≃S k → i ≃S k
transS L L {One x} {One x₁} {One x₂} p q = trans p q
transS L (B c₁ c₂) {Row i i₁} {Row j j₁} {Row k k₁} (p , q) (p' , q') =
  transS L c₁ p p' , transS L c₂ q q'
transS (B r₁ r₂) L {Col i i₁} {Col j j₁} {Col k k₁} (p , q) (p' , q') =
  transS r₁ L p p' , transS r₂ L q q'
transS (B r₁ r₂) (B c₁ c₂) {Q i₂ i i₃ i₁} {Q j₂ j j₃ j₁} {Q k k₁ k₂ k₃}
  (p , q , x , y) (p' , q' , x' , y') =
  transS r₁ c₁ p p' , transS r₁ c₂ q q' ,
  transS r₂ c₁ x x' , transS r₂ c₂ y y'

assocS : (r c : Shape) (x y z : M s r c) → ((x +S y) +S z) ≃S (x +S (y +S z))
assocS L L (One x) (One y) (One z) = assocs x y z
assocS L (B c c₁) (Row x x₁) (Row y y₁) (Row z z₁) =
  assocS L c x y z  , assocS L c₁ x₁ y₁ z₁
assocS (B r r₁) L (Col x x₁) (Col y y₁) (Col z z₁) =
  assocS r L x y z , assocS r₁ L x₁ y₁ z₁
assocS (B r r₁) (B c c₁) (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
  (assocS r c x y z) , (assocS r c₁ x₁ y₁ z₁) ,
  (assocS r₁ c x₂ y₂ z₂) , (assocS r₁ c₁ x₃ y₃ z₃)

<+S> : (r c : Shape) {x y u v : M s r c} →
  x ≃S y → u ≃S v → (x +S u) ≃S (y +S v)
<+S> L L {One x} {One x₁} {One x₂} {One x₃} p q = p <+> q
<+S> L (B c c₁) {Row x x₁} {Row y y₁} {Row u u₁} {Row v v₁} (p , p₁) (q , q₁) =
  <+S> L c p q , <+S> L c₁ p₁ q₁
<+S> (B r r₁) L {Col x x₁} {Col y y₁} {Col u u₁} {Col v v₁} (p , p₁) (q , q₁) =
  <+S> r L p q , <+S> r₁ L p₁ q₁
<+S> (B r r₁) (B c c₁) {Q x x₁ x₂ x₃} {Q y y₁ y₂ y₃} {Q u u₁ u₂ u₃} {Q v v₁ v₂ v₃}
  (p , p₁ , p₂ , p₃) (q , q₁ , q₂ , q₃) =
  <+S> r c p q , <+S> r c₁ p₁ q₁ ,
  <+S> r₁ c p₂ q₂ , <+S> r₁ c₁ p₃ q₃

identSˡ : (r c : Shape) (x : M s r c) →
   zerS r c +S x ≃S x
identSˡ L L (One x) = identityˡs x
identSˡ L (B c c₁) (Row x x₁) = identSˡ L c x , identSˡ L c₁ x₁
identSˡ (B r r₁) L (Col x x₁) = identSˡ r L x , identSˡ r₁ L x₁
identSˡ (B r r₁) (B c c₁) (Q x x₁ x₂ x₃) =
  identSˡ r c x , identSˡ r c₁ x₁ ,
  identSˡ r₁ c x₂ , identSˡ r₁ c₁ x₃

commS : (r c : Shape) → (x y : M s r c) →
  (x +S y) ≃S (y +S x)
commS L L (One x) (One x₁) = comms x x₁
commS L (B c c₁) (Row x x₁) (Row y y₁) = (commS L c x y) , (commS L c₁ x₁ y₁)
commS (B r r₁) L (Col x x₁) (Col y y₁) = (commS r L x y) , (commS r₁ L x₁ y₁)
commS (B r r₁) (B c c₁) (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) =
  commS r c x y , commS r c₁ x₁ y₁ ,
  commS r₁ c x₂ y₂ , commS r₁ c₁ x₃ y₃

-- used to make proofs nicer later on
setoidS : {r c : Shape} → Setoid _ _
setoidS {r} {c} =
  record
    { Carrier = M s r c
    ; _≈_ = _≃S_ {r} {c}
    ; isEquivalence =
      record
        { refl = reflS r c ; sym = symS r c ; trans = transS r c } }
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
identSʳ :  (r : Shape) (c : Shape) (x : M s r c) →
           x +S zerS r c ≃S x
identSʳ r c x =
  let open EqReasoning setoidS
  in begin
    x +S zerS r c
  ≈⟨ commS r c x (zerS r c) ⟩
    zerS r c +S x
  ≈⟨ identSˡ r c x ⟩
    x
  ∎
\end{code}

%if False
\begin{code}
zerolHelp : ∀ (r : Shape) {m m' c : Shape}
  (x : M s m c)
  (y : M s m' c) →
  zerS r m *S x   ≃S  zerS r c  →
  zerS r m' *S y  ≃S  zerS r c  →
  zerS r m *S x +S zerS r m' *S y  ≃S  zerS r c
zerolHelp r {m} {m'} {c} x y p q =
  let open EqReasoning setoidS
  in begin
    zerS r m *S x +S zerS r m' *S y
  ≈⟨ <+S> _ _ {zerS r m *S x} {zerS r c} {zerS r m' *S y} {zerS r c} p q ⟩
    zerS r c +S zerS r c
  ≈⟨ identSˡ _ _ (zerS r c) ⟩
   zerS r c
  ∎

zeroSˡ : (a b c : Shape) (x : M s b c) →
  (zerS a b *S x) ≃S zerS a c
zeroSˡ L L L (One x) = zeroˡ x
zeroSˡ L L (B c c₁) (Row x x₁) = (zeroSˡ L L c x) , (zeroSˡ L L c₁ x₁)
zeroSˡ L (B b b₁) L (Col x x₁) =
  zerolHelp L x x₁ (zeroSˡ L b L x) (zeroSˡ L b₁ L x₁)
zeroSˡ L (B b b₁) (B c c₁) (Q x x₁ x₂ x₃) =
  zerolHelp L x x₂ (zeroSˡ L b c x) (zeroSˡ L b₁ c x₂) ,
  zerolHelp L x₁ x₃ (zeroSˡ L b c₁ x₁) (zeroSˡ L b₁ c₁ x₃)
zeroSˡ (B a a₁) L L (One x) =
  zeroSˡ a L L (One x) ,
  zeroSˡ a₁ L L (One x)
zeroSˡ (B a a₁) L (B c c₁) (Row x x₁) =
  zeroSˡ a L c x ,
  zeroSˡ a L c₁ x₁ ,
  zeroSˡ a₁ L c x ,
  zeroSˡ a₁ L c₁ x₁
zeroSˡ (B a a₁) (B b b₁) L (Col x x₁) =
  zerolHelp a x x₁ (zeroSˡ a b L x) (zeroSˡ a b₁ L x₁) ,
  zerolHelp a₁ x x₁ (zeroSˡ a₁ b L x) (zeroSˡ a₁ b₁ L x₁)
zeroSˡ (B a a₁) (B b b₁) (B c c₁) (Q x x₁ x₂ x₃) =
  zerolHelp a x x₂ (zeroSˡ a b c x) (zeroSˡ a b₁ c x₂) ,
  zerolHelp a x₁ x₃ (zeroSˡ a b c₁ x₁) (zeroSˡ a b₁ c₁ x₃) ,
  zerolHelp a₁ x x₂ (zeroSˡ a₁ b c x) (zeroSˡ a₁ b₁ c x₂) ,
  zerolHelp a₁ x₁ x₃ (zeroSˡ a₁ b c₁ x₁) (zeroSˡ a₁ b₁ c₁ x₃)

zerorHelp : ∀ r {m m' c}
  (x : M s r m)
  (x₁ : M s r m') →
  x *S zerS m c ≃S zerS r c →
  x₁ *S zerS m' c ≃S zerS r c →
  x *S zerS m c +S x₁ *S zerS m' c
  ≃S zerS r c
zerorHelp r {m} {m'} {c} x x₁ p q =
  let open EqReasoning setoidS
  in begin
    x *S zerS m c +S x₁ *S zerS m' c
  ≈⟨ <+S> _ _ {x *S zerS m c} {zerS r c} {x₁ *S zerS m' c} {zerS r c} p q ⟩
    zerS r c +S zerS r c
  ≈⟨ identSˡ r c (zerS r c) ⟩
    zerS r c
  ∎

zeroSʳ : (a b c : Shape) (x : M s a b) →
  (x *S zerS b c) ≃S zerS a c
zeroSʳ L L L (One x) = zeroʳ x
zeroSʳ L L (B c c₁) (One x) =
  (zeroSʳ L L c (One x)) ,
  (zeroSʳ L L c₁ (One x))
zeroSʳ L (B b b₁) L (Row x x₁) =
  zerorHelp L {c = L} x x₁ (zeroSʳ L b L x) (zeroSʳ L b₁ L x₁)
zeroSʳ L (B b b₁) (B c c₁) (Row x x₁) =
  zerorHelp L {c = c} x x₁ (zeroSʳ L b c x) (zeroSʳ L b₁ c x₁) ,
  zerorHelp L {c = c₁} x x₁ (zeroSʳ L b c₁ x) (zeroSʳ L b₁ c₁ x₁)
zeroSʳ (B a a₁) L L (Col x x₁) =
  zeroSʳ a L L x ,
  zeroSʳ a₁ L L x₁
zeroSʳ (B a a₁) L (B c c₁) (Col x x₁) =
  zeroSʳ a L c x ,
  zeroSʳ a L c₁ x ,
  zeroSʳ a₁ L c x₁ ,
  zeroSʳ a₁ L c₁ x₁
zeroSʳ (B a a₁) (B b b₁) L (Q x x₁ x₂ x₃) =
  zerorHelp a x x₁ (zeroSʳ a b L x) (zeroSʳ a b₁ L x₁) ,
  zerorHelp a₁ x₂ x₃ (zeroSʳ a₁ b L x₂) (zeroSʳ a₁ b₁ L x₃)
zeroSʳ (B a a₁) (B b b₁) (B c c₁) (Q x x₁ x₂ x₃) =
  zerorHelp a x x₁ (zeroSʳ a b c x) (zeroSʳ a b₁ c x₁) ,
  zerorHelp a x x₁ (zeroSʳ a b c₁ x) (zeroSʳ a b₁ c₁ x₁) ,
  zerorHelp a₁ x₂ x₃ (zeroSʳ a₁ b c x₂) (zeroSʳ a₁ b₁ c x₃) ,
  zerorHelp a₁ x₂ x₃ (zeroSʳ a₁ b c₁ x₂) (zeroSʳ a₁ b₁ c₁ x₃)

<*S> : (a b c : Shape) {x y : M s a b} {u v : M s b c} →
  x ≃S y → u ≃S v → (x *S u) ≃S (y *S v)
<*S> L L L {One x} {One x₁} {One x₂} {One x₃} p q = p <*> q
<*S> L L (B c c₁) {One x} {One x₁} {Row u u₁} {Row v v₁} p (q , q₁) =
  (<*S> L L c {One x} {One x₁} {u} {v} p q) ,
  <*S> L L c₁ {One x} {One x₁} {u₁} {v₁} p q₁
<*S> L (B b b₁) L {Row x x₁} {Row y y₁} {Col u u₁} {Col v v₁} (p , p₁) (q , q₁) =
  let
    open EqReasoning setoidS
    ih = <*S> _ _ _ {x} {y} {u} {v} p q
    ih₁ = <*S> _ _ _ {x₁} {y₁} {u₁} {v₁} p₁ q₁
  in begin
    Row x x₁ *S Col u u₁
  ≡⟨ refl-≡ ⟩
    x *S u +S x₁ *S u₁
  ≈⟨ <+S> L L {x *S u} {y *S v} {x₁ *S u₁} {y₁ *S v₁} ih ih₁ ⟩
    y *S v +S y₁ *S v₁
  ∎
<*S> L (B b b₁) (B c c₁) {Row x x₁} {Row y y₁}
     {Q u u₁ u₂ u₃} {Q v v₁ v₂ v₃}
     (p , p₁) (q , q₁ , q₂ , q₃) =
  (let
    ih = <*S> L b c p q
    ih₁ = <*S> L b₁ c p₁ q₂
  in <+S> L c ih ih₁) ,
  <+S> L c₁ (<*S> L b c₁ p q₁) (<*S> L b₁ c₁ p₁ q₃)
<*S> (B a a₁) L L {Col x x₁} {Col y y₁} {One x₂} {One x₃} (p , p₁) q =
  <*S> a L L p q ,
  <*S> a₁ L L p₁ q
<*S> (B a a₁) L (B c c₁) {Col x x₁} {Col y y₁} {Row u u₁} {Row v v₁} (p , p₁) (q , q₁) =
  <*S> a L c p q ,
  <*S> a L c₁ p q₁  ,
  <*S> a₁ L c p₁ q ,
  <*S> a₁ L c₁ p₁ q₁
<*S> (B a a₁) (B b b₁) L {Q x x₁ x₂ x₃} {Q y y₁ y₂ y₃} {Col u u₁} {Col v v₁} (p , p₁ , p₂ , p₃) (q , q₁) =
  <+S> a L (<*S> a b L p q) (<*S> a b₁ L p₁ q₁) ,
  <+S> a₁ L (<*S> a₁ b L p₂ q) (<*S> a₁ b₁ L p₃ q₁ )
<*S> (B a a₁) (B b b₁) (B c c₁) {Q x x₁ x₂ x₃} {Q y y₁ y₂ y₃} {Q u u₁ u₂ u₃} {Q v v₁ v₂ v₃} (p , p₁ , p₂ , p₃) (q , q₁ , q₂ , q₃) =
  <+S> a c (<*S> a b c p q) (<*S> a b₁ c p₁ q₂) ,
  <+S> a c₁ (<*S> a b c₁ p q₁) (<*S> a b₁ c₁ p₁ q₃) ,
  <+S> a₁ c (<*S> a₁ b c p₂ q) (<*S> a₁ b₁ c p₃ q₂) ,
  <+S> a₁ c₁ (<*S> a₁ b c₁ p₂ q₁) (<*S> a₁ b₁ c₁ p₃ q₃)

idemS : (r c : Shape) (x : M s r c) → x +S x ≃S x
idemS L L (One x) = idem x
idemS L (B c c₁) (Row x x₁) = (idemS _ _ x) , (idemS _ _ x₁)
idemS (B r r₁) L (Col x x₁) = (idemS _ _ x) , (idemS _ _ x₁)
idemS (B r r₁) (B c c₁) (Q x x₁ x₂ x₃) =
  (idemS _ _ x) , (idemS _ _ x₁ , (idemS _ _ x₂  , idemS _ _ x₃))

swapMid : {r c : Shape} (x y z w : M s r c) →
  (x +S y) +S (z +S w) ≃S (x +S z) +S (y +S w)
swapMid {r} {c} x y z w =
  let open EqReasoning setoidS
  in begin
    (x +S y) +S (z +S w)
  ≈⟨ assocS _ _ x y (z +S w) ⟩
    x +S y +S z +S w
  ≈⟨ <+S> r c (reflS r c) (symS r c (assocS r c y z w)) ⟩
    x +S (y +S z) +S w
  ≈⟨ <+S> r c (reflS r c) (<+S> r c (commS r c y z) (reflS r c)) ⟩
    x +S (z +S y) +S w
  ≈⟨ <+S> r c (reflS r c) (assocS r c z y w) ⟩
    x +S z +S y +S w
  ≈⟨ symS r c (assocS r c x z (y +S w)) ⟩
    (x +S z) +S (y +S w)
  ∎

distlHelp : ∀ {a b b₁ c₁}
            (x : M s a b)
            (y z : M s b c₁)
            (x₁ : M s a b₁)
            (y₁ z₁ : M s b₁ c₁) →
          (x *S (y +S z)) ≃S (x *S y +S x *S z) →
          (x₁ *S (y₁ +S z₁)) ≃S (x₁ *S y₁ +S x₁ *S z₁) →
          (x *S (y +S z) +S x₁ *S (y₁ +S z₁))
          ≃S ((x *S y +S x₁ *S y₁) +S x *S z +S x₁ *S z₁)
distlHelp x y z x₁ y₁ z₁ p q =
  let open EqReasoning setoidS
  in begin
    x *S (y +S z) +S x₁ *S (y₁ +S z₁)
  ≈⟨ <+S> _ _ {x *S (y +S z)} {x *S y +S x *S z}
              {x₁ *S (y₁ +S z₁)} {x₁ *S y₁ +S x₁ *S z₁} p q ⟩
    (x *S y +S x *S z) +S x₁ *S y₁ +S x₁ *S z₁
  ≈⟨ swapMid (x *S y) (x *S z) (x₁ *S y₁) (x₁ *S z₁) ⟩
    (x *S y +S x₁ *S y₁) +S x *S z +S x₁ *S z₁
  ∎

distlS : {a b c : Shape} (x : M s a b) (y z : M s b c) →
  (x *S (y +S z)) ≃S ((x *S y) +S (x *S z))
distlS {L} {L} {L} (One x) (One y) (One z) = distl x y z
distlS {L} {L} {B c c₁} (One x) (Row y y₁) (Row z z₁) =
  distlS (One x) y z ,
  distlS (One x) y₁ z₁
distlS {L} {(B b b₁)} {L} (Row x x₁) (Col y y₁) (Col z z₁) =
  distlHelp x y z x₁ y₁ z₁ (distlS x y z) (distlS x₁ y₁ z₁)
distlS {L} {(B b b₁)} {(B c c₁)} (Row x x₁) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
  distlHelp x y z x₁ y₂ z₂ (distlS x y z) (distlS x₁ y₂ z₂) ,
  distlHelp x y₁ z₁ x₁ y₃ z₃  (distlS x y₁ z₁) (distlS x₁ y₃ z₃)
distlS {(B a a₁)} {L} {L} (Col x x₁) (One x₂) (One x₃) =
  distlS x (One x₂) (One x₃) ,
  distlS x₁ (One x₂) (One x₃)
distlS {(B a a₁)} {L} {(B c c₁)} (Col x x₁) (Row y y₁) (Row z z₁) =
  distlS x y z ,
  distlS x y₁ z₁ ,
  distlS x₁ y z ,
  distlS x₁ y₁ z₁
distlS {(B a a₁)} {(B b b₁)} {L} (Q x x₁ x₂ x₃) (Col y y₁) (Col z z₁) =
  distlHelp x y z x₁ y₁ z₁ (distlS x y z) (distlS x₁ y₁ z₁) ,
  distlHelp x₂ y z x₃ y₁ z₁ (distlS x₂ y z) (distlS x₃ y₁ z₁)
distlS {(B a a₁)} {(B b b₁)} {(B c c₁)} (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
  distlHelp x y z x₁ y₂ z₂ (distlS x y z) (distlS x₁ y₂ z₂) ,
  distlHelp x y₁ z₁ x₁ y₃ z₃ (distlS x y₁ z₁) (distlS x₁ y₃ z₃) ,
  distlHelp x₂ y z x₃ y₂ z₂ (distlS x₂ y z) (distlS x₃ y₂ z₂)  ,
  distlHelp x₂ y₁ z₁ x₃ y₃ z₃ (distlS x₂ y₁ z₁) (distlS x₃ y₃ z₃)

distrHelp : ∀ {r m m₁ c : Shape}
            (x : M s m c)
            (y z : M s r m)
            (x₁ : M s m₁ c)
            (y₁ z₁ : M s r m₁) →
          ((y +S z) *S x) ≃S (y *S x +S z *S x) →
          ((y₁ +S z₁) *S x₁) ≃S (y₁ *S x₁ +S z₁ *S x₁) →
          ((y +S z) *S x +S (y₁ +S z₁) *S x₁)
          ≃S ((y *S x +S y₁ *S x₁) +S z *S x +S z₁ *S x₁)
distrHelp x y z x₁ y₁ z₁ p q =
  let open EqReasoning setoidS
  in begin
    (y +S z) *S x +S (y₁ +S z₁) *S x₁
  ≈⟨ <+S> _ _ {(y +S z) *S x} {y *S x +S z *S x}
              {(y₁ +S z₁) *S x₁} {y₁ *S x₁ +S z₁ *S x₁} p q ⟩
    (y *S x +S z *S x) +S y₁ *S x₁ +S z₁ *S x₁
  ≈⟨ swapMid (y *S x) (z *S x) (y₁ *S x₁) (z₁ *S x₁) ⟩
    (y *S x +S y₁ *S x₁) +S z *S x +S z₁ *S x₁
  ∎

distrS : {r m c : Shape} (x : M s m c) (y z : M s r m) →
  ((y +S z) *S x) ≃S ((y *S x) +S (z *S x))
distrS {L} {L} {L} (One x) (One y) (One z) =
  distr x y z
distrS {L} {L} {B c c₁} (Row x x₁) (One x₂) (One x₃) =
  (distrS x (One x₂) (One x₃)) ,
  (distrS x₁ (One x₂) (One x₃))
distrS {L} {B m m₁} {L} (Col x x₁) (Row y y₁) (Row z z₁) =
  distrHelp x y z x₁ y₁ z₁ (distrS x y z) (distrS x₁ y₁ z₁)
distrS {L} {B m m₁} {B c c₁} (Q x x₁ x₂ x₃) (Row y y₁) (Row z z₁) =
  (distrHelp x y z x₂ y₁ z₁ (distrS x y z) (distrS x₂ y₁ z₁)) ,
  (distrHelp x₁ y z x₃ y₁ z₁ (distrS x₁ y z) (distrS x₃ y₁ z₁))
distrS {B r r₁} {L} {L} (One x) (Col y y₁) (Col z z₁) =
  distrS (One x) y z ,
  distrS (One x) y₁ z₁
distrS {B r r₁} {L} {B c c₁} (Row x x₁) (Col y y₁) (Col z z₁) =
  (distrS x y z) ,
  (distrS x₁ y z) ,
  (distrS x y₁ z₁) ,
  (distrS x₁ y₁ z₁)
distrS {B r r₁} {B m m₁} {L} (Col x x₁) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
  (distrHelp x y z x₁ y₁ z₁ (distrS x y z) (distrS x₁ y₁ z₁)) ,
  (distrHelp x y₂ z₂ x₁ y₃ z₃ (distrS x y₂ z₂) (distrS x₁ y₃ z₃))
distrS {B r r₁} {B m m₁} {B c c₁} (Q x x₁ x₂ x₃) (Q y y₁ y₂ y₃) (Q z z₁ z₂ z₃) =
  distrHelp x y z x₂ y₁ z₁ (distrS x y z) (distrS x₂ y₁ z₁) ,
  distrHelp x₁ y z x₃ y₁ z₁ (distrS x₁ y z) (distrS x₃ y₁ z₁) ,
  distrHelp x y₂ z₂ x₂ y₃ z₃ (distrS x y₂ z₂) (distrS x₂ y₃ z₃) ,
  distrHelp x₁ y₂ z₂ x₃ y₃ z₃ (distrS x₁ y₂ z₂) (distrS x₃ y₃ z₃)

distrS' : {r m c : Shape} (x : M s m c) (y z : M s r m) →
  ((y *S x) +S (z *S x)) ≃S ((y +S z) *S x)
distrS' {r} {m} {c} x y z = symS r c (distrS x y z)
\end{code}

Finally we are able to lift the semi-near-ring to a semi-near-ring of
matrices (see the module \texttt{LiftSNR} for the full proof), however
we can only lift to a square matrix (i.e.\ the same shape in both
dimensions).
\begin{figure}[h!]
\begin{multicols}{2}
\begin{code}
Square : Shape → SemiNearRing
Square shape = SNR
  where

  isEquivS =
    record
      { refl   = reflS shape shape
      ; sym    = symS shape shape
      ; trans  = transS shape shape }

  isSemgroupS =
    record
      { isEquivalence  = isEquivS
      ; assoc          = assocS shape shape
      ; ∙-cong         = <+S> shape shape }

  isCommMonS =
    record
      { isSemigroup  = isSemgroupS
      ; identityˡ    = identSˡ shape shape
      ; comm         = commS shape shape }

\end{code}
\columnbreak
\begin{code}

  SNR : SemiNearRing
  SNR =
    record
      { s = S
      ; _≃s_ = _≃S_ {shape} {shape}
      ; zers = zerS shape shape
      ; _+s_ = _+S_
      ; _*s_ = _*S_
      ; isCommMon = isCommMonS
      ; zeroˡ = zeroSˡ shape shape shape
      ; zeroʳ = zeroSʳ shape shape shape
      ; _<*>_ = <*S> shape shape shape
      ; idem = idemS shape shape
      ; distl = distlS {shape} {shape}
      ; distr = distrS {shape} {shape}
      }
\end{code}
\end{multicols}
\caption{Lifting a semi-near-ring to a matrix of square shape.}
\end{figure}
%endif
