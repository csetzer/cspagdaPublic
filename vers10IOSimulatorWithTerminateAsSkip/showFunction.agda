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


showMayLab : Maybe Label → String
showMayLab (just l) = showLabel l
showMayLab nothing  = "τ"

showProLab : { i : Size} → {c : Choice}  → Process i c  → String
showProLab (terminate x) = ""
showProLab (node P) = unlinesWithChosenString 
                     " "
                     ((mapL (λ c → extChoiceElToName (choice2Str c)
                                    ++s ":" 
                                    ++s showLabel (Lab P c))
                          (choice2Enum (E P)))
                      ++
                      (mapL (λ c → intChoiceElToName (choice2Str c)
                                    ++s ":" 
                                    ++s "τ")
                          (choice2Enum (I P))))

                       

  


show✓ : { i : Size} → {c : Choice}  → Process i c  → String
show✓ (node P) = unlinesWithChosenString 
                     " "
                     (mapL (λ t → (terminationChoiceElToName (choice2Str t )
                                    ++s ":" 
                                    ++s choice2Str (PT P t))) 
                          (choice2Enum (T P)))
show✓ (terminate a) = ""


proChoiceIs∅ : { i : Size} → {c : Choice}  → Process i c  → Bool
proChoiceIs∅ (node P) = choiceIsEmpty (E P) ∧ choiceIsEmpty (I P)
proChoiceIs∅ (terminate x) = true


proHasSuccessfullyTerminated : { i : Size} → {c : Choice}  → Process i c  → Bool
proHasSuccessfullyTerminated (node P) = false
proHasSuccessfullyTerminated (terminate x) = true


proToE : ∀ {i} → {c : Choice} → Process i c → Choice
proToE (node P) = E P
proToE (terminate x) = fin 0


proToI : ∀ {i} → { c : Choice } → Process i c → Choice
proToI (node P) = I P
proToI (terminate x) = fin 0

proPToSubPro∞ : ∀ {i} → {c : Choice} 
                      → (P : Process i c) 
                      → ChoiceSet (proToE P) ⊎ ChoiceSet (proToI P)
                      → Process∞ i c 
proPToSubPro∞ (node P) (inj₁ c') = PE P c'
proPToSubPro∞ (node P) (inj₂ c') = PI P c'
proPToSubPro∞ (terminate x) (inj₁ ())
proPToSubPro∞ (terminate x) (inj₂ ())



proPToSubPrP : ∀ {i} → {j : Size< i} → {c : Choice} 
                      → (P : Process i c) 
                      → ChoiceSet (proToE P) ⊎ ChoiceSet (proToI P)
                      → Process j c
proPToSubPrP {i} {j} {c} P c' = forcep (proPToSubPro∞  {i} {c} P c') 



choiceFunToStr : {c₀ : Choice} → (c : Choice) 
                         → (g : ChoiceSet c → ChoiceSet c₀) → String
choiceFunToStr {c₀} c g = unlinesWithChosenString 
                                 " " 
                                 (mapL  (λ x →  "(λ " 
                                                 ++s choice2Str x 
                                                 ++s " → " 
                                                 ++s choice2Str (g x) 
                                                 ++s ")")  
                                        (choice2Enum c))

choiceFunToStr↓ : {c₀ : Choice} → {c : Choice}
                         → (g : ChoiceSet c → ChoiceSet c₀) → String
choiceFunToStr↓ {c₀} {c} g = choiceFunToStr {c₀} c g

choice2Str2Str : {c : Choice} → (f : ChoiceSet c → String)  → String
choice2Str2Str {c} f = unlinesWithChosenString " " (mapL ((λ x → "(λ "  
                                                                  ++s (choice2Str x) 
                                                                  ++s " → " 
                                                                  ++s f x 
                                                                  ++s ")")) 
                               (choice2Enum c))




