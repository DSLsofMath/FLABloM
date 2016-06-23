% -*- latex -*-
%let submit = True
%\documentclass{sigplanconf}
\documentclass[preprint]{sigplanconf}

%%% Standard definitions from the lhs2TeX installation
%include polycode.fmt

%%% Put your own formatting directives in a separate file
%include paper.format

\usepackage{amsmath}
\usepackage{url}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{stmaryrd}
\usepackage{hyperref}
\usepackage{tikz}
\usepackage{subcaption}

\bibliographystyle{abbrvnat}

%%% Some useful macros
%if submit
\newcommand{\todo}[2][?]{}
%else
\newcommand{\todo}[2][?]{\marginpar{\raggedright \tiny TODO: #2}}
%endif

\setcounter{secnumdepth}{0}

\input{matrix} % definitions for matrix printing

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{Type-driven Development}{September 18, 2016, Nara, Japan}
\copyrightyear{2016}
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm} %TODO
\copyrightdoi{nnnnnnn.nnnnnnn} %TODO

\titlebanner{Preprint}                      % These are ignored unless
\preprintfooter{In submission to TyDe'16}   % 'preprint' option specified.

\todo{Make the title fit the contents better: A formalization of ... closure ... block}
% \title{Extended Abstract\\ FLABloM: Functional Linear Algebra with
%   Block Matrices}
\title{Extended abstract: An Agda formalisation of the transitive
  closure of block matrices}

\authorinfo{Adam Sandberg Eriksson \and Patrik Jansson}
           {Chalmers University of Technology, Sweden}
           {\{saadam,patrikj\}@@chalmers.se}

%\titlerunning{Functional linear algebra with block matrices}
%\authorrunning{Adam Sandberg Eriksson \& Patrik Jansson}

\maketitle

%\tableofcontents

% \abstract{%
%   We define a block based matrix representation in Agda and lift
%   various algebraic structures (semi-near-rings, semi-rings and closed
%   semi-rings) to matrices in order to verify algorithms that can be
%   implemented using the closure operation in a semi-ring.}

% \section{Introduction}
% \label{sec:intro}

\category{D.1.1}{Programming Techniques}{Applicative (Functional) Programming}
%\category{D.2.4}{SOFTWARE ENGINEERING}{Software/Program Verification}
\category{F.3.1}{Logics and Meanings of Programs}{Specifying and
   Verifying and Reasoning about Programs} % [Logics of programs]

% \category{F.3.1}{Logics and Meanings of Programs}{Specifying and
%   Verifying and Reasoning about Programs} % [Logics of programs]
% \category{D.3.2}{Programming Languages}{Language Classifications }[Applicative (functional) languages]

% Something about testing should be added

% Some other remotely related categories:

% \category{F.3.3}{Logics and Meanings of Programs}{Studies
%   of Program Constructs}[Program and recursion schemes,
%   Type structure]

% \category{F.3.2}{Logics and Meanings of Programs}{Semantics
%   of Programming Languages}[Denotational Semantics]

% \category{D.3.1}{Programming Languages}{Formal Definitions
%   and Theory}[Semantics]

% \category{F.4.1}{Mathematical Logic and Formal
%   Languages}{Mathematical Logic}[Model theory, Proof
%   theory, Lambda calculus and related systems]

% \category{F.3.3}{Logics and Meanings of Programs}{Studies of Program Constructs}[Type Structure]



% TODO: ovan är gissningar efter snabb läsning av
% http://www.acm.org/about/class/ccs98-html

%TODO: uncomment some proof fragment

In \cite{bernardy2015certified} Bernardy \& Jansson used a recursive
block formulation of matrices to certify Valiant's
\cite{valiant_general_1975} parsing algorithm.
%
Their matrix formulation was restricted to matrices of size
\(2^n \times 2^n\) and this work extends the matrix formulation to allow
for all sizes of matrices and applies similar techniques to algorithms
that can be described as transitive closures of semi-rings of matrices
with inspiration from \cite{dolan2013fun} and \cite{lehmann1977}.

\paragraph{Development structure}

To structure the formal development we define a hierarchy of ring
structures as Agda records:
%
A semi-near-ring for some type |s| needs an equivalence relation |≃s|,
a distinguished element |zers| and operations addition |+s| and
multiplication |*s|.
%
Our semi-near-ring requires that
%
|zers| and |+s| form a commutative monoid (i.e. |+s| commutes and
|zers| is the left and right identity of |+s|),
%
|zers| is the left and right zero of |*s|,
%
|+s| is idempotent (|∀ x → x +s x ≃s x|) and
%
|*s| distributes over |+s|.

For the semi-ring we extend the semi-near-ring with another
distinguished element |ones| and proofs that |*s| is associative and
that |ones| is the left and right identity of |*s|.

Finally we extend the semi-ring with an operation |closure| that
computes the transitive closure of an element of the semi-ring (|c| is
the closure of |w| if |c ≃s ones +s w *s c| holds), we denote the
closure of \(w\) with \(w^*\).

We use two examples of semi-rings with transitive closure:
%
(1) the Booleans with disjunction as addition, conjunction as
multiplication and the closure being |true|; and
%
(2) the natural numbers (|ℕ|) extended with an element |∞|, we let
|zers = ∞|, |ones = 0|, |min| plays the role of |+s|, addition of
natural numbers the role of |*s| and the closure is~|0|.

\paragraph{Matrices}

%include ../Shape.lagda

%include ../Matrix.lagda

%include ../LiftSNR.lagda

\paragraph{Transitive closure}

%include ../LiftCSR.lagda

\paragraph{Graph reachability}

Using this definition of transitive closure of matrices instantiated
with the boolean semi-ring defined above we get an implementation of a
graph reachability algorithm.
%
If we have a graph (figure~\ref{fig:graph1}) and its incidence matrix
(as below)
%
we can find all reachable nodes (figure~\ref{fig:graph2}) by
computing the transitive closure of the incidence matrix.

\[
  \left.\Quad[3ex]
    {\Quad{0}{0}
      {0}{0}}
    {\Quad{0}{0}
      {0}{1}}
    {\Quad{0}{1}
      {0}{0}}
    {\Quad{0}{0}
      {0}{0}}
  \right.^*
  =
  \Quad[3ex]
  {\Quad{1}{0}
    {0}{1}}
  {\Quad{0}{0}
    {0}{1}}
  {\Quad{0}{1}
    {0}{0}}
  {\Quad{1}{1}
    {0}{1}}
\]

\begin{figure}[h]\centering
  \begin{subfigure}{0.2\textwidth}\centering
    \begin{tikzpicture}[->]
      \node (1) {1}; \node (2) [right of=1] {2}; \node (3) [below
      of=1] {3}; \node (4) [below of=2] {4}; \path (3) edge (2) (2)
      edge (4);
    \end{tikzpicture}
    \caption{A graph}
    \label{fig:graph1}
  \end{subfigure}
  \quad
  \begin{subfigure}{0.2\textwidth}\centering
    \begin{tikzpicture}[->]
      \node (1) {1}; \node (2) [right of=1] {2}; \node (3) [below
      of=1] {3}; \node (4) [below of=2] {4}; \path (3) edge (2) (2)
      edge (4) (3) edge (4) (1) edge [loop above] (1) (2) edge [loop
      above] (2) (3) edge [loop below] (3) (4) edge [loop below] (4);
    \end{tikzpicture}
    \caption{Reachable nodes}
    \label{fig:graph2}
  \end{subfigure}
  \caption{Graph with reachable nodes}
\end{figure}


\paragraph{Conclusions}
We have presented an algebraic structure useful for (block) matrix
computations and implemented and proved correctness of transitive
closure.
%
Compared to \cite{bernardy2015certified} our implementation handles
arbitrary matrix dimensions but is restricted to semi-rings.
%
Future work would be to extend the proof to cover both arbitrary
dimensions and the more general semi-near-ring structure which would
allow parallel parsing as an application.

% TODO: The bibliography should be embedded for final submission.

\bibliography{paper}

\end{document}
