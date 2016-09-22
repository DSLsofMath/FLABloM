% -*- latex -*-
%let submit = True
\documentclass{beamer}

%%% Standard definitions from the lhs2TeX installation
%include polycode.fmt

%%% Put your own formatting directives in a separate file
%include paper.format

\usepackage{amsmath}
\usepackage{url}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
% \usepackage{unicode-math}
\usepackage{autofe}
\usepackage{latexsym}
\usepackage{stmaryrd}
\usepackage{multicol}
\usepackage{hyperref}
%\usepackage{textgreek}
\usepackage{tikz}

%%% Some useful macros
%if submit
\newcommand{\todo}[2][?]{}
%else
\newcommand{\todo}[2][?]{\marginpar{\raggedright \tiny TODO: #2}}
%endif

\newcommand{\TODO}[1]{\todo{#1}}
\newcommand{\refSec}[1]{Sec. \ref{#1}}
\newcommand{\refSecs}[1]{Secs. \ref{#1}}
\newcommand{\refSecI}[1]{Section \ref{#1}}
\newcommand{\refSecsI}[1]{Sections \ref{#1}}
\newcommand{\refTab}[1]{Tab. \ref{#1}}

\setcounter{secnumdepth}{0}

\setbeamertemplate{navigation symbols}{}


\input{matrix}

\newcommand{\A}{%
  \Quad[2mm]{1}         {\Row{0}{1}}
            {\Col{0}{0}}{\Quad{1}{1}
                              {0}{1}}%
}
\newcommand{\B}{%
  \Quad[2mm]{0}         {\Row{1}{2}}
            {\Col{0}{0}}{\Quad{1}{7}
                              {3}{8}}%
}
\newcommand{\C}{%
  \Quad[2mm]{2}         {\Row{1}{0}}
            {\Col{1}{0}}{\Quad{9}{8}
                              {7}{6}}%
}
\newcommand{\D}{%
  \Quad[2mm]{1}         {\Row{0}{1}}
            {\Col{0}{0}}{\Quad{1}{1}
                              {0}{1}}%
}

\begin{document}

\title{An Agda formalisation of the transitive closure of block matrices}
\author{\underline{Adam Sandberg Eriksson} \and Patrik Jansson}
\institute{
  Chalmers University of Technology,
  Sweden\\
  \texttt{\{saadam,patrikj\}@@chalmers.se}}

% \titlerunning{Functional linear algebra with block matrices}
% \authorrunning{Adam Sandberg Eriksson \& Patrik Jansson}
% \date{2016-06-14, IFIP WG 2.1 meeting \#74}
\date{2016-09-18\\ 1st Workshop on Type-Driven Development}

\frame{\titlepage}

\begin{frame}
  \frametitle{Transitive closure of block matrices}

  \begin{itemize}
  \item Inspired by work on parallel parsing by Bernardy \& Jansson
  \item Matrices in Agda
  \item Reflexive, transitive closure of matrices
  \end{itemize}

%\centering
\[
  \Quad[10mm]{\A}{\B}
             {\C}{\D}
\]
\end{frame}

\begin{frame}
  \frametitle{Towards a datatype for matrices}

  Desirable:

  \begin{itemize}
  \item Easy to program with
  \item Easy to write proofs with
  \end{itemize}
\pause
  Possibilities:

  \begin{itemize}
  \item Vectors of vectors: |Vec (Vec a n) m|
  \item Functions from indices: |Fin m → Fin n → a|
  \item \dots
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Matrix ``shapes''}

A type for shapes (generalisation of natural numbers):

\begin{code}
data Shape : Set where
  L  : Shape
  B  : Shape → Shape → Shape

two     = B L L
three   = B two L
three'  = B L two
\end{code}

\pause

Shapes for one dimension: a vector/row matrix with shape |B (B L L) L|

\[
\Row{\Row{1}{3}}{16}
\]
\end{frame}

\newcommand{\emptybox}{\ensuremath{\boxed{\phantom{x}}}}
\begin{frame}
  \frametitle{Matrices: building blocks}

  Matrices are indexed by two shapes:

\begin{code}
data M (a : Set) : (rows cols : Shape) → Set
\end{code}
\pause
{\footnotesize
\[
\begin{array}{cccc}
\emptybox,\qquad &
%
\Row{\emptybox}{\emptybox},\qquad &
%
\Col[1ex]{\emptybox}{\emptybox},\qquad &
%
\Quad[1ex]{\emptybox}{\emptybox}
     {\emptybox}{\emptybox}
 \\ \\
|M a L L|
& |M a L (B c₁ c₂)|
& |M a (B r₁ r₂) L|
& |M a (B r₁ r₂) (B c₁ c₂)|
\end{array}
\]
}
\end{frame}


\begin{frame}
  \frametitle{Matrices: a datatype}

\begin{code}
data M (a : Set) : (rows cols : Shape) → Set where
  One :  a → M a L L

  Col :  {r₁ r₂ : Shape} →
         M a r₁ L → M a r₂ L → M a (B r₁ r₂) L

  Row :  {c₁ c₂ : Shape} →
         M a L c₁ → M a L c₂ →  M a L (B c₁ c₂)

  Q   :  {r₁ r₂ c₁ c₂ : Shape} →
         M a r₁ c₁ → M a r₁ c₂ →
         M a r₂ c₁ → M a r₂ c₂ →
         M a (B r₁ r₂) (B c₁ c₂)
\end{code}
\end{frame}

\begin{frame}
  \frametitle{Development structure}

  A hierarchy of rings as Agda records:

  \begin{itemize}
  \item |SemiNearRing|

    |≃|, |+|, $\cdot$, |0|\qquad(+ is associative and commutes, 0 identity of + and zero of
    $\cdot$, $\cdot$~distributes~over~+)

  \item |SemiRing|

    1\qquad(1 identity of $\cdot$, $\cdot$ is associative)

  \item |ClosedSemiRing|

    an operation $^*$ with $w^* ≃ 1 + w \cdot w^*$.
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Lifting matrices}

  We take a semi-(near)-ring and lift it to square matrices.

  A lifting function for each |Shape| and ring structure.

  \begin{code}
    LiftSNR    : Shape  → SemiNearRing    → SemiNearRing
    LiftSR     : Shape  → SemiRing        → SemiRing
    LiftCSR    : Shape  → ClosedSemiRing  → ClosedSemiRing
  \end{code}
\end{frame}

\begin{frame}
  \frametitle{Lifting matrices}

  Lifting equivalence:

  \begin{code}
    _≃S_ : ∀ {r c} → M s r c → M s r c → Set
    (One x)     ≃S (One x₁)    =  x ≃s x₁
    (Row m m₁)  ≃S (Row n n₁)  =  (m ≃S n) × (m₁ ≃S n₁)
    (Col m m₁)  ≃S (Col n n₁)  =  (m ≃S n) × (m₁ ≃S n₁)
    (Q m00  m01  m10  m11)  ≃S (Q n00  n01  n10  n11)  =
     (m00 ≃S n00) × (m01 ≃S n01) ×
     (m10 ≃S n10) × (m11 ≃S n11)
  \end{code}
\end{frame}

\begin{frame}
  \frametitle{Lifting matrices}

  (Parts of) matrix multiplication:

  \begin{code}
    _*S_ : ∀ {r m c} → M s r m → M s m c → M s r c
    One x      *S One y       = One (x *s y)
    Row m0 m1  *S Col n0 n1   = m0 *S n0 +S m1 *S n1
    Col m0 m1  *S Row n0 n1   = Q  (m0 *S n0)   (m0 *S n1)
                                   (m1 *S n0)   (m1 *S n1)
  \end{code}
  \[\vdots\]

\end{frame}

\begin{frame}
  \frametitle{Closure for matrices}

Computing the reflexive, transitive closure:

{\small
\centering
\begin{align*}
  \left.\boxed{a}\right.^* & = \boxed{a^*} \\
  \left.
  \Quad[1ex]{A_{11}}{A_{12}}
            {A_{21}}{A_{22}}
  \right.^*
  & =
  \Quad[2ex]{A_{11}^* + A_{11}^* \cdot A_{12} \cdot \Delta^* \cdot A_{21} \cdot A_{11}^*}
            {\quad A_{11}^* \cdot A_{12} \cdot \Delta^*}
            {\Delta^* \cdot A_{21} \cdot A_{11}^*}
            {\Delta^*}
\end{align*}
}

\qquad ($\Delta = A_{22} + A_{21} \cdot A_{11}^* \cdot A_{12}$)

with a constructive proof that it satisfies $w^* ≃ 1 + w \cdot w^*$

% add example!
% what if you have to explain this algorithm?
\end{frame}

\begin{frame}
  \frametitle{Reachability example}

  A closed semi--ring of booleans:

  \begin{align*}
    |zers| & = |false| \\
    |ones| & = |true| \\
    |+s|   & = \lor \\
    |*s|   & = \land \\
    b^*    & = |true|
  \end{align*}
\end{frame}

\begin{frame}
  \frametitle{Reachability example}


  \begin{align*}
    \left(
    \begin{tikzpicture}[->,baseline=-3.5ex]
      \node (1) {1};
      \node (2) [right of=1] {2};
      \node (3) [below of=1] {3};
      \node (4) [below of=2] {4};
      \path
      (3) edge (2)
      (2) edge (4);
    \end{tikzpicture}
    \right)^*
    \quad & \onslide<2->{ = \quad
      \begin{tikzpicture}[->,baseline=-3.5ex]
        \node (1) {1};
        \node (2) [right of=1] {2};
        \node (3) [below of=1] {3};
        \node (4) [below of=2] {4};
        \path
        (3) edge (2)
        (2) edge (4)
        (3) edge (4)
        (1) edge [loop above] (1)
        (2) edge [loop above] (2)
        (3) edge [loop below] (3)
        (4) edge [loop below] (4);
      \end{tikzpicture}}
      \\
    \left.
    \Quad[3ex]{\Quad{0}{0}
    {0}{0}}
    {\Quad{0}{0}
    {0}{1}}
    {\Quad{0}{1}
    {0}{0}}
    {\Quad{0}{0}
    {0}{0}}\right.^*
    \quad & \onslide<2->{ = \quad
      \Quad[3ex]{\Quad{1}{0}
      {0}{1}}
      {\Quad{0}{0}
      {0}{1}}
      {\Quad{0}{1}
      {0}{0}}
      {\Quad{1}{1}
      {0}{1}}}
  \end{align*}

  \onslide<3->{
    \[w^* = 1 + w + w^2 + \dots\]
  }
\end{frame}

\begin{frame}
  \frametitle{Related work}

  \begin{itemize}
  \item Bernardy \& Jansson: ``Certified Context-Free Parsing: A
    formalisation of Valiant's Algorithm in Agda''
  \item Dolan: ``Fun with Semirings''
  \end{itemize}
\end{frame}

\begin{frame}
  \frametitle{Wrapping up}

  \begin{itemize}
  \item This matrix definition is not the final word
  \item A more flexible matrix definition: sparse? fewer constructors?
  \item Mapping from efficient storage to matrix-datatype.
  \item Automation (of proofs)!
  \item Performance/complexity of closure algorithm.
  \item Generalisation to closed semi-near-ring for parsing
    applications.
  \item Agda development available at
    \url{https://github.com/DSLsofMath/FLABloM}.
  \end{itemize}

\end{frame}

% \begin{frame}
%   \frametitle{Complexity}
% \end{frame}

% \begin{frame}
%   \frametitle{Closure example}
% \end{frame}

\end{document}
