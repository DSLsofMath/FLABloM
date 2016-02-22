% -*- latex -*-

%let submit = False
\documentclass[a4paper]{easychair}

%%% Standard definitions from the lhs2TeX installation
%include polycode.fmt
%%% Put your own formatting directives in a separate file
%include paper.format

\usepackage{url}
% \usepackage{ucs}
% \usepackage[utf8x]{inputenc}
\usepackage{unicode-math}
% \usepackage{autofe}
\usepackage{stmaryrd}
\usepackage{multicol}
% \usepackage{hyperref}

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

%\toappear{}

% \usepackage[style=abbrvnat]{biblatex}
% %%% Keep references in a separate bib-file
% \addbibresource{paper.bib}

\setcounter{secnumdepth}{0}

\begin{document}

\title{FLABloM: Functional linear algebra with block matrices}
\author{Adam Sandberg Eriksson \and Patrik Jansson}
\institute{
  Chalmers University of Technology,
  Sweden\\
  \email{\{saadam,patrikj\}@@chalmers.se}}

\titlerunning{Functional linear algebra with block matrices}
\authorrunning{Adam Sandberg Eriksson \& Patrik Jansson}

\maketitle

%%% Some venues require ACM classification categories - here is an example
% \category{D.1.1}%
%   {Programming Techniques}%
%   {Applicative (Functional) Programming}%

% \terms
% design, languages, verification

% \keywords
% some, important, concepts, not already, mentioned, in the title

%\tableofcontents

\abstract{%
  We define a block based matrix representation in Agda and lift
  various algebraic structures (semi-near-rings, semi-rings and closed
  semi-rings) to matrices in order to verify algorithms that can be
  implemented using the closure operation in a semi-ring.}

\section{Introduction}
\label{sec:intro}

In \cite{bernardy2015certified} Bernardy \& Jansson used a clever
formulation of matrices to certify Valiant's
\cite{valiant_general_1975} parsing algorithm.
%
Their matrix formulation was restricted to matrices of size
$2^n \times 2^n$ and this work extends the matrix formulation to allow
for all sizes of matrices and applies the techniques to other
algorithms that can be described as closed semi-near-rings with
inspiration from \cite{dolan2013fun} and \cite{lehmann1977}.

We define a hierarchy of ring structures as Agda records. A
semi-near-ring for some type |s| needs an equivalence relation |≃s|, a
distinguished element |zers| and operations addition |+s| and
multiplication |*s|.
%
Our semi-near-ring requires proofs that
\begin{itemize}
\item |zers| and |+s| form a commutative monoid (i.e. |+s| commutes
  and |zers| is the left and right identity of |+s|),
\item |zers| is the left and right zero of |*s|,
\item |+s| is idempotent (|∀ x → x +s x ≃s x|) and
\item |*s| distributes over |+s|.
\end{itemize}

For the semi-ring we extend the semi-near-ring with an element |ones|
and proofs that |*s| is associative and that |ones| is the left and
right identity of |*s|.

Finally we extend the semi-ring with an operation |closure| that
computes the transitive closure of an element of the semi-ring (|c| is
the closure of |w| if |c ≃s ones +s w *s c| holds), we denote the
closure with $^*$.

We use two examples of closed semi-rings:
%
(1) the Booleans with disjunction as addition, conjunction as
multiplication and the closure being |true|; and
%
(2) the natural numbers (|ℕ|) extended with an element |∞|, we let
|zers = ∞|, |ones = 0|, |min| plays the role of |+s|, addition of
natural numbers the role of |*s| and the closure is 0.

\section{Matrices}

%include ../Shape.lagda

%include ../Matrix.lagda

\paragraph{Transitive closure}

%include ../LiftCSR.lagda

% TODO: how we instantiate the matrix with one of the rings described
% above to get "interesting" algorithms.

% \paragraph{Acknowledgements} Many thanks to Patrik Jansson for for the
% inspiration for this project and guidance in implementation.

\bibliographystyle{plain}
\bibliography{paper}
\end{document}
