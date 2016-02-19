module Reachability where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality

open import SemiNearRingRecord
open import SemiRingRecord
open import ClosedSemiRingRecord

open import Matrix
open import Shape
open import BoolRing
open import LiftCSR using (Square)

-- 4 nodes in graph
shape : Shape
shape = B (B L L) (B L L)

open ClosedSemiRing (Square BoolCSR shape)
open SemiRing sr
open SemiNearRing snr

T = One true
F = One false

{-
1   2
   /|
  / |
 /  |
3   4
-}
graph : s
graph =
  Q (Q T F
       F T)
    (Q F F
       T T)
    (Q F T
       F T)
    (Q T F
       F T)

can-reach = closure graph

g = Q (Q T F
         F T)
      (Q F F
         T T)
      (Q F T
         F T)
      (Q T T
         T T)

p : can-reach ≡ g
p = refl
