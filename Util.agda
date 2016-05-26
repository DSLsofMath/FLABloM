module Util where

open import Data.Bool
open import Data.String

open import Matrix
open import Shape

b2s : Bool → String
b2s false = "0"
b2s true = "1"

bracket : String → String
bracket s = "\\left[ " ++ s ++ " \\right]"

tex : ∀ {r c} (m : M Bool r c) → String
tex (One x) = b2s x
tex (Row m m₁) = bracket ("\\begin{array}{cc}\n" ++ tex m ++ " &\n" ++ tex m₁ ++ "\\end{array}")
tex (Col m m₁) = bracket ("\\begin{array}{c}\n" ++ tex m ++ " \\\\\n" ++ tex m₁ ++ "\\end{array}")
tex (Q m m₁ m₂ m₃) = bracket
  ("\\begin{array}{cc}\n" ++ tex m ++ " & " ++ tex m₁ ++ " \\\\\n"
    ++ tex m₂ ++ " & " ++ tex m₃
    ++ "\\end{array}")

tex' : ∀ {r c} (m : M Bool r c) → Costring
tex' m = toCostring (tex m)

open import IO.Primitive
open import Reachability

main =
  putStrLn (tex' graph) >>= λ _ → putStrLn (tex' can-reach)
