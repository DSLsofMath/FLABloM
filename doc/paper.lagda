% -*- latex -*-

%let submit = False
%if submit
\documentclass[onecolumn,times,authoryear]{sigplanconf}
%else
\documentclass[onecolumn,preprint,times]{sigplanconf}
%endif

%%% Standard definitions from the lhs2TeX installation
%include polycode.fmt
%%% Put your own formatting directives in a separate file
%include paper.format

\usepackage{url}
% \usepackage{ucs}
% \usepackage[utf8x]{inputenc}
\usepackage{unicode-math}
\usepackage{autofe}
\usepackage{stmaryrd}
\usepackage{multicol}
\usepackage{hyperref}

%if techreport
\usepackage{TRtitlepage}
%endif

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

\toappear{}

% \usepackage[style=abbrvnat]{biblatex}
% %%% Keep references in a separate bib-file
% \addbibresource{paper.bib}



\begin{document}

%if submit
\conferenceinfo{}{}
\CopyrightYear{}
\copyrightdata{}
%elif not techreport
\titlebanner{Preprint}
\preprintfooter{Preprint}
%endif

%if techreport
\TRtitlepage
  {The title}             % argument 1 <= the title
  {Tess Ting \\[1em] Test Ing} % argument 2 <= authors
  {}                                     % argument 3 <= report number
%else
\title{Functional linear algebra with block matrices}

\authorinfo{Adam Sandberg Eriksson}
           {Chalmers Univeristy of Technology, Sweden}
           {\texttt{saadam@@chalmers.se}}

\maketitle
%endif


%-------------------------------------------------------------------------------

\begin{abstract}
  The abstract should describe in a short and catchy way what the paper
  is about etc.
  \begin{itemize}
  \item block matrices
  \item linear algebra
  \item rings (semi-near-rings, semi-rings, \dots)
  \item closure of matrices
  \end{itemize}

TODO: decide on spelling in the text part: Currently mixed: ``semi-ring'' (here), ``semiring'' (in SemiRingRecord.lagda), ``SemiRing'', ``semi ring'' (in ClosedSemiRingRecord.lagda)
\end{abstract}

%%% Some venues require ACM classification categories - here is an example
% \category{D.1.1}%
%   {Programming Techniques}%
%   {Applicative (Functional) Programming}%

\terms
design, languages, verification

\keywords
some, important, concepts, not already, mentioned, in the title

%\tableofcontents

\section{Introduction}
\label{sec:intro}

In \cite{bernardy2015certified} a formulation of matrices was
used to certify the Valiant parsing algorithm.
%
The matrix formulation used was restricted to matrices of size
$2^n \times 2^n$.
%
This work extends the matrix to allow for all sizes of matrices and
applies the techniques to other algorithms that can be described as
semirings or semi-near-rings with inspiration from \cite{dolan2013fun}.

\section{Structures}
\label{sec:structs}

We define a hierarchy of rings as records in Agda. Using algebraic
structures from the Agda standard library a record for semi-near-rings
is built and then extended for semi-rings and closed semi-rings.

The Agda defintions of these three structures are found below and in
modules \texttt{SemiNearRingRecord}, \texttt{SemiRingRecord} and
\texttt{ClosedSemiRingRecord}.

\subsection{Seminearring}
%include ../SemiNearRingRecord.lagda

\subsection{Semiring}
%include ../SemiRingRecord.lagda

\subsection{Closed semiring}
%include ../ClosedSemiRingRecord.lagda

\subsection{Examples}

Two examples of structures that are closed semirings are the booleans
and the natural numbers extended with $\infty$ (known as the tropical
semiring).
%
If we use either of these as the elements of a matrix we can compute
properties of graphs such as the reachability between nodes (using the
boolean semiring) and the distance between nodes (using the tropical
semiring).

The booleans form a closed semiring with disjunction $\vee$ as
addition and conjunction $\land$ as multiplication. The closure of a
booleans is defined to be |true|.

The tropical semiring uses |min| as addition and addition of natural
numbers as multiplication. The closure is defined to be 0.

The definition and proofs are found in the modules \texttt{BoolRing}
and \texttt{TropicalRing}.

\section{Matrices}

%include ../Shape.lagda

%include ../Matrix.lagda

\section{Lifting}

The main work of this project is to lift the above defined structures,
semi-near-rings, semi-rings and closed semi-rings, to matrices where
the base elements are the carrier type of the lifted ring.

%include ../LiftSNR.lagda

Lifting to a semi-ring follows the same pattern, adding only the
|ones| and proofs that |ones| is the left and right identity of
|_*s_|.

\section{Transitive closure of matrices}

%include ../LiftCSR.lagda

\section{Conclusions and further work}
\label{sec:conc}

There is very often a conclusion section.
%
Not so much in this skeleton!

\paragraph{Acknowledgements.} This research has been partially funded
by the (some project title + granting agency).
%
Somebody helped with something.
%
The reviewers suggested many improvements to the paper.

%------------------------------------------------------------------------------
\bibliographystyle{abbrvnat}
\bibliography{paper}
\end{document}
