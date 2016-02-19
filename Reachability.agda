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

one : Shape
one = L
two : Shape
two = B one one
four : Shape
four = B two two

open ClosedSemiRing (Square BoolCSR four)
open SemiRing sr
open SemiNearRing snr

M1 = M Bool one one
M2 = M Bool two two
M4 = M Bool four four

T : M1
T = One true
F : M1
F = One false


{-
1   2
   /|
  / |
 /  |
3   4
-}

edgeless2 :  M2
edgeless2 =  Q F F
               F F
diagonal2 :  M2
diagonal2 =  Q T F
               F T
full2     :  M2
full2     =  Q T T
               T T

graph : M4
graph =
  Q edgeless2    (Q F F
                    T T)
    (Q F T
       F T)      edgeless2

can-reach = closure graph

g = Q diagonal2  (Q F F
                    T T)
      (Q F T
         F T)    full2


p : can-reach ≡ g
p = refl
