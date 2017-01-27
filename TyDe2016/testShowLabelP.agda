module testShowLabelP where

open import showLabelP
open import Data.String renaming (_++_ to _++s_)
open import Data.List
open import label



s0 : String
s0 = unlinesWithChosenString " "  ("" ∷ [])

s1 : String
s1 = unlinesWithChosenString " "  ("ab" ∷ [])

s2 : String
s2 = unlinesWithChosenString " "  ("ab" ∷ [])


s3 : String
s3 = unlinesWithChosenString " "  ("ab" ∷ "cd" ∷ [])

s4 : String
s4 = unlinesWithChosenString "-> "  ("ab" ∷ "cd" ∷ [])



f : Label → Label
f laba = labb
f labb = labc
f labc = laba

s5 : String
s5 = labelLabelFunToString f


