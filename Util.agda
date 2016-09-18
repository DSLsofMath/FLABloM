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
tex (Row m m₁) = "\\Row{" ++ tex m ++ "}{" ++ tex m₁ ++ "}"
tex (Col m m₁) = "\\Col{" ++ tex m ++ "}{" ++ tex m₁ ++ "}"
tex (Q m m₁ m₂ m₃) =
  "\\Quad{" ++ tex m ++ "}{" ++ tex m₁ ++ "}{"
            ++ tex m₂ ++ "}{" ++ tex m₃ ++ "}"

tex' : ∀ {r c} (m : M Bool r c) → Costring
tex' m = toCostring (tex m)

open import IO.Primitive
open import Reachability

main =
  putStrLn (tex' graph) >>= λ _ → putStrLn (tex' can-reach)
