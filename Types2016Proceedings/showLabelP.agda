module showLabelP where

open import label
open import Data.String renaming (_++_ to _++s_)
open import Data.String.Base
open import Data.Bool
open import Data.List.Base
open import Data.List
open import libraryList

unlinesWithChosenString : String → List String → String
unlinesWithChosenString s [] = ""
unlinesWithChosenString s (s' ∷ []) = s'
unlinesWithChosenString s (s' ∷ s'' ∷ l) = s' ++s s ++s unlinesWithChosenString s (s'' ∷ l)


showLabel : Label → String
showLabel laba = "a"
showLabel labb = "b"
showLabel labc = "c"


LabelList : List Label
LabelList = laba ∷ labb ∷ labc ∷ []


labelBoolFunToString : (Label → Bool) →  String
labelBoolFunToString f = unlines (map showLabel (filterBool f  LabelList))



labelLabelFunToString : (Label → Label) →  String
labelLabelFunToString f = "[["
                          ++s unlinesWithChosenString ", " (map (λ l → showLabel (f l) ++s " <- " ++s showLabel l) LabelList )
                          ++s "]]"
