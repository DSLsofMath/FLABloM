module Everything where

-- Preliminaries

import Preliminaries  -- some definitions, borrowed from Valiant Agda
import Product        -- non-dependent products


-- Ring structures

import SemiNearRingRecord
import SemiRingRecord
import ClosedSemiNearRingRecord
import ClosedSemiRingRecord


-- Matrices

import Shape          -- datatype of matrix dimensions
import Matrix         -- datatype of matrices


-- Rings

import BoolRing       -- Bool as a closed semi-ring
import TropicalRing   -- ℕ + ∞ as a closed semi-ring


-- Matrices as closed semi-rings

import LiftSNR        -- lifts semi-near-rings
import LiftSR         -- lifts semi-rings
import LiftCSR        -- lifts closed semi-rings
