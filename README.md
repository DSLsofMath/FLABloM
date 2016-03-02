# FLABloM: Functional linear algebra with block matrices

[Extended abstract](http://www.cse.chalmers.se/~patrikj/papers/FLABloM_TYPES_2016_preprint.pdf) submitted to [TYPES 2016](http://www.types2016.uns.ac.rs/).

# Overview

The development is structured using a hierarchy of Agda records
implementing semi-near-rings, semi-rings and closed semi-rings.

- Preliminaries

    - [Preliminaries.lagda](Preliminaries.lagda) -- some definitions,
      borrowed from [Valiant Agda][1].
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



# FLABloM: Functional Linear Algebra with Block Matrices

A project instance of
  [DAT235 - Research-oriented special course](https://www.student.chalmers.se/sp/course?course_id=23301)
for Adam SE during study period 2, 2015.

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
