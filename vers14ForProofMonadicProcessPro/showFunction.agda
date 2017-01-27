module showFunction where

open import process
open Process∞
open Process+
open import label
open import auxData
open import choiceSetU
open import Size
open import Data.List
open import Data.List.Base renaming (map to mapL)
open import Data.String renaming (_++_ to _++s_)
open import showLabelP
open import choiceAuxFunction
open import Data.Bool renaming (T to True)
open import Data.Maybe
open import Data.Sum

showMaybeLabel : Maybe Label → String
showMaybeLabel (just l) = showLabel l
showMaybeLabel nothing  = "τ"


{-
printOptionAux : {E I : Choice} → List (String × ChoiceSet E) → (l : ChoiceSet E → Label) → List ( String × ChoiceSet I) → String 
printOptionAux [] l [] = ""
printOptionAux {E} {I} [] l ((x ,, x₁) ∷ L) =     intChoiceElToName x ++s ":" ++s "τ"  ++s " " ++s   printOptionAux {E} {I} [] l L 
printOptionAux {c} ((x ,, x₁) ∷ L) l L' = extChoiceElToName x ++s ":" ++s showLabel (l x₁)  ++s " " ++s   printOptionAux {c} L l L'


showLabels₁ : { i : Size} → {c : Choice}  → Process i c  → String
showLabels₁ (node P) = printOptionAux {E P} {I P} (choice2EnumStr (E P)) (Lab P) (choice2EnumStr (I P))
showLabels₁ (terminate x) = ""
-}

showLabels₁ : { i : Size} → {c : Choice}  → Process i c  → String
showLabels₁ (terminate x) = ""
showLabels₁ (node P) = unlinesWithChosenString 
                     " "
                     ((mapL (λ c → extChoiceElToName (choice2Str c)
                                    ++s ":" 
                                    ++s showLabel (Lab P c))
                          (choice2Enum (E P)))
                      ++
                      (mapL (λ c → extChoiceElToName (choice2Str c)
                                    ++s ":" 
                                    ++s "τ")
                          (choice2Enum (I P))))

                       


showTicks : { i : Size} → {c : Choice}  → Process i c  → String
showTicks (node P) = unlinesWithChosenString 
                     " "
                     (mapL (λ t → (choice2Str t 
                                    ++s ":" 
                                    ++s choice2Str (PT P t))) 
                          (choice2Enum (T P)))
showTicks (terminate a) = ""

processChoiceIsEmpty : { i : Size} → {c : Choice}  → Process i c  → Bool
processChoiceIsEmpty (node P) = choiceIsEmpty (E P) ∧ choiceIsEmpty (I P)
processChoiceIsEmpty (terminate x) = true


processHasSuccessfullyTerminated : { i : Size} → {c : Choice}  → Process i c  → Bool
processHasSuccessfullyTerminated (node P) = false
processHasSuccessfullyTerminated (terminate x) = true


processToE : ∀ {i} → {c : Choice} → Process i c → Choice
processToE (node P) = E P
processToE (terminate x) = fin 0


processToI : ∀ {i} → { c : Choice } → Process i c → Choice
processToI (node P) = I P
processToI (terminate x) = fin 0

processToExternalSubprocess0 : ∀ {i} → {c : Choice} 
                                     → (P : Process i c) 
                                     → ChoiceSet (processToE P) ⊎ ChoiceSet (processToI P)
                                     → Process∞ i c 
processToExternalSubprocess0 (node P) (inj₁ c') = PE P c'
processToExternalSubprocess0 (node P) (inj₂ c') = PI P c'
processToExternalSubprocess0 (terminate x) (inj₁ ())
processToExternalSubprocess0 (terminate x) (inj₂ ())



choiceFunctionToString : {c₀ : Choice} → (c : Choice) 
                         → (g : ChoiceSet c → ChoiceSet c₀) → String
choiceFunctionToString {c₀} c g = unlinesWithChosenString 
                                 " " 
                                 (mapL  (λ x →  "(λ " 
                                                 ++s choice2Str x 
                                                 ++s " → " 
                                                 ++s choice2Str (g x) 
                                                 ++s ")")  
                                        (choice2Enum c))

choiceFunctionToStringi : {c₀ : Choice} → {c : Choice}
                         → (g : ChoiceSet c → ChoiceSet c₀) → String
choiceFunctionToStringi {c₀} {c} g = choiceFunctionToString {c₀} c g

choice2Str2Str : {c : Choice} → (f : ChoiceSet c → String)  → String
choice2Str2Str {c} f = unlinesWithChosenString " " (mapL ((λ x → "(λ "  
                                                                  ++s (choice2Str x) 
                                                                  ++s " → " 
                                                                  ++s f x 
                                                                  ++s ")")) 
                               (choice2Enum c))


{- Probably Obsolete -}

{-
funcChoice2ProcessToProcess : ∀ {i} → (c d : Choice) → (ChoiceSet c  → Process i d) → String
funcChoice2ProcessToProcess c d f = unlines (mapL ((λ x → "λ "  ++s (choice2Str x) ++s " → " ++s Str (f x) ++s ")"))
                                    (choice2Enum c))

funcChoice2ProcessToProcess∞ : ∀ {i} → (c d : Choice) → (ChoiceSet c  → Process∞ (↑ i)  d) → String
funcChoice2ProcessToProcess∞ {i} c d f = funcChoice2ProcessToProcess c d (λ x → forcep (f x ) {i} )

funcChoice2ProcessToProcess∞' : ∀ {i} → {c d : Choice} → (ChoiceSet c  → Process∞ (↑ i)  d) → String
funcChoice2ProcessToProcess∞' {i} {c} {d} f = funcChoice2ProcessToProcess∞ c d f

funcChoice2ProcessToProcess₁ : ∀ {i} → {c₀ : Choice} → (c : Choice) 
                              → (ChoiceSet c  → Process i c₀) 
                              → String
funcChoice2ProcessToProcess₁ {i} {c₀} c f = unlines (mapL ((λ x → "(λ "  ++s (choice2Str x) ++s " → " ++s Str (f x) ++s ")")) (choice2Enum c))


funcChoice2ProcessToProcess₁∞ : ∀ {i}  → {c₀ : Choice} → (c : Choice) 
                                → (ChoiceSet c  → Process∞ (↑ i)  c₀) 
                                → String
funcChoice2ProcessToProcess₁∞ {i} c f = funcChoice2ProcessToProcess₁ c (λ x → forcep (f x ) {i} )

-}



{-
showProcess : {i : Size} →  (c : Choice) → Process i (ChoiceSet c)   → String
showProcess c (node P)      = Str P
showProcess c (terminate a) = choice2Str a


showProcess0 : {i : Size} →  {c : Choice} → Process i (ChoiceSet c)   → String
showProcess0 {i} {c} p = showProcess {i} c p

showProcess∞ : {i : Size} →  {c : Choice} → Process∞  (↑ i) (ChoiceSet c)   → String
showProcess∞ {i} {c} P = showProcess {i} c (forcep P {i})
-}


processToSubprocess0 : ∀ {i} → {c : Choice} 
                      → (P : Process i c) 
                      → ChoiceSet (processToE P) ⊎ ChoiceSet (processToI P)
                      → Process∞ i c 
processToSubprocess0 (node P) (inj₁ c') = PE P c'
processToSubprocess0 (node P) (inj₂ c') = PI P c'
processToSubprocess0 (terminate x) (inj₁ ())
processToSubprocess0 (terminate x) (inj₂ ())



processToSubprocess : ∀ {i} → {j : Size< i} → {c : Choice} 
                      → (P : Process i c) 
                      → ChoiceSet (processToE P) ⊎ ChoiceSet (processToI P)
                      → Process j c
processToSubprocess  {i} {j} {c} P c' = forcep (processToSubprocess0  {i} {c} P c') 

