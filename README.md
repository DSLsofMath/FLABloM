# FLABloM: Functional linear algebra with block matrices

Associated material for some work on block based matrix representation
in Agda. We lift various algebraic structures (semi-near-rings,
semi-rings and closed semi-rings) to matrices in order to verify
algorithms that can be implemented using the closure operation in a
semi-ring.

## [TyDe 2016: Type-driven Development](http://conf.researchr.org/track/icfp-2016/tyde-2016-papers)

- Extended abstract accepted for TyDe 2016: "An Agda Formalisation of the Transitive Closure of Block Matrices (Extended Abstract)"
    - [preprint](http://www.cse.chalmers.se/~patrikj/papers/AgdaClosureBlock_TyDe16.pdf)
- This work was partially supported by the projects [GRACeFUL (grant agreement No 640954)](https://www.graceful-project.eu/) and [CoeGSS (grant agreement No 676547)](http://coegss.eu/), which have received funding from the European Union’s Horizon 2020 research and innovation programme.

## [TYPES 2016](http://www.types2016.uns.ac.rs/) presentation

- Title: "FLABloM: Functional linear algebra with block matrices"
- [Extended abstract](http://www.types2016.uns.ac.rs/images/abstracts/eriksson.pdf)
- [Accepted](http://www.types2016.uns.ac.rs/index.php/programme-2/accepted)
  for presentation at [TYPES 2016](http://www.types2016.uns.ac.rs/).
- Conf. pres.:
  [Thursday 2016-05-26 at 15.00](http://www.types2016.uns.ac.rs/index.php/programme-2/conf-prog)
  -- [slides](http://www.types2016.uns.ac.rs/images/Slides/A.Eriksson.pdf)
- (Dry-run: Friday 2016-05-19 at 11.00 in EDIT-6128, Chalmers)

## Overview

The development is structured using a hierarchy of Agda records
implementing semi-near-rings, semi-rings and closed semi-rings.

- Preliminaries

    - [Preliminaries.lagda](Preliminaries.lagda) -- some definitions,
      borrowed from [ValiantAgda][1].
    - [Product.lagda](Product.lagda) -- non-dependent product.

- Structures

    Agda records for our ring hierarchy.

    - [SemiNearRingRecord.lagda](SemiNearRingRecord.lagda)
    - [SemiRingRecord.lagda](SemiRingRecord.lagda)
    - [ClosedSemiNearRingRecord.lagda](ClosedSemiNearRingRecord.lagda)
    - [ClosedSemiRingRecord.lagda](ClosedSemiRingRecord.lagda)

- Matrix

    - [Shape.lagda](Shape.lagda) -- datatype of matrix dimensions
    - [Matrix.lagda](Matrix.lagda) -- datatype of matrices

- Rings

    - [BoolRing.lagda](BoolRing.lagda) -- Bool as a closed semi-ring
    - [TropicalRing.lagda](TropicalRing.lagda) -- ℕ + ∞ as a closed semi-ring

- Matrices as rings

    Lifts some ring structure to a matrix ring of said structure

    - [LiftSNR.lagda](LiftSNR.lagda) -- Lift semi-near-rings
    - [LiftSR.lagda](LiftSR.lagda) -- Lift semi-rings
    - [LiftCSNR.lagda](LiftCSNR.lagda) -- Lift closed semi-near-rings (not finished)
    - [LiftCSR.lagda](LiftCSR.lagda) -- Lift closed semi-rings

- Documentation

    - [abstract.lagda](doc/abstract.lagda) -- abstract submitted to TYPES 2016
    - [paper.lagda](doc/paper.lagda) -- unfinished technical report (longer version
      of abstract)
    - [slides.lagda](doc/slides.lagda) -- slides used for presentation
      at TYPES 2016 and WG2.1 meeting 2016

## Project course instance at Chalmers

Project title: "FLABloM: Functional Linear Algebra with Block Matrices"

A project instance of
  [DAT235 - Research-oriented special course](https://www.student.chalmers.se/sp/course?course_id=23301)
for Adam SE during study period 2 (Nov-Dec), 2015.

## Builds on courses

Discrete mathematics, Linear algebra, Advanced functional programming,
Types for programs and proofs.

## Project summary

A [recent paper][1] by Bernardy and Jansson has explored Parallel Parsing
formulated in terms of matrix algebra. The formulation is based on a
recursive decomposition of "large" matrices into 2x2 block matrices
which enables short and concise algorithm formulation, sparse matrix
representation and simplified proofs of correctness. The aim of this
project is to explore to what degree this idea can be back-ported to
classical linear algebra with the aim to influence the DSLsofMath
course.

[1]: http://wiki.portal.chalmers.se/cse/pmwiki.php/FP/ValiantAgda

ValiantAgda Code: https://github.com/DSLsofMath/ValiantAgda
