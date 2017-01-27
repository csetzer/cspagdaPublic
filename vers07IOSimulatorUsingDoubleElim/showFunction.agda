module showFunction where

open import process
open Process∞
open Process+
open import label
open import auxData
open import choiceSetU
open import Size
open import Data.List
open import Data.String renaming (_++_ to _++s_)
open import showLabelP
open import choiceAuxFunction
open import Data.Bool
open import Data.Maybe
open import Data.Sum

showMaybeLabel : Maybe Label → String
showMaybeLabel (just l) = showLabel l
showMaybeLabel nothing  = "τ"



showProcess : {i : Size} →  (c : Choice) → Process i (ChoiceSet c)   → String
showProcess c (node P)      = Str P
showProcess c (terminate a) = choice2String c a


showProcess0 : {i : Size} →  {c : Choice} → Process i (ChoiceSet c)   → String
showProcess0 {i} {c} p = showProcess {i} c p

showProcess∞ : {i : Size} →  {c : Choice} → Process∞  (↑ i) (ChoiceSet c)   → String
showProcess∞ {i} {c} P = showProcess {i} c (forcep P i)


printOptionAux : {E I : Choice} → List (String × ChoiceSet E) → (l : ChoiceSet E → Label) → List ( String × ChoiceSet I) → String 
printOptionAux [] l [] = ""
printOptionAux {E} {I} [] l ((x ,, x₁) ∷ L) =  intChoiceElToName x ++s ":" ++s "τ"  ++s " " ++s   printOptionAux {E} {I} [] l L 
printOptionAux {c} ((x ,, x₁) ∷ L) l L' = extChoiceElToName x ++s ":" ++s showLabel (l x₁)  ++s " " ++s   printOptionAux {c} L l L'


showLabels₁ : { i : Size} → {A : Set}  → Process i A  → String
showLabels₁ (node P) = printOptionAux {E P} {I P} (choice2Enumeration (E P)) (Lab P) (choice2Enumeration (I P))
-- showLabels₁ (node E Lab PE I PI Stat) = printOptionAux {E} {I} (choice2Enumeration E) Lab (choice2Enumeration I)

showLabels₁ (terminate x) = ""


processChoiceIsEmpty : { i : Size} → {A : Set}  → Process i A  → Bool
processChoiceIsEmpty (node P) = choiceIsEmpty (E P) ∧ choiceIsEmpty (I P)
processChoiceIsEmpty (terminate x) = true

processHasSuccessfullyTerminated : { i : Size} → {A : Set}  → Process i A  → Bool
processHasSuccessfullyTerminated (node P) = false
processHasSuccessfullyTerminated (terminate x) = true



processToE : ∀ {i} → { A : Set } → Process i A → Choice
processToE (node P) = E P
processToE (terminate x) = fin 0


processToI : ∀ {i} → { A : Set } → Process i A → Choice
processToI (node P) = I P
processToI (terminate x) = fin 0

processToExternalSubprocess0 : ∀ {i} → {A : Set} 
                                     → (P : Process i A) 
                                     → ChoiceSet (processToE P) ⊎ ChoiceSet (processToI P)
                                     → Process∞ i A 
processToExternalSubprocess0 (node P) (inj₁ c') = PE P c'
processToExternalSubprocess0 (node P) (inj₂ c') = PI P c'
processToExternalSubprocess0 (terminate x) (inj₁ ())
processToExternalSubprocess0 (terminate x) (inj₂ ())

{-
test : Set
test = {!printOptionAux (choice2Enumeration (namedElements ("A" ∷ "B" ∷ [])))  (λ l → laba)!}
-}
