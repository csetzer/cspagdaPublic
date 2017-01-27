module skip where 

open import Size
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import Data.List
open import process
open import auxData
open import dataAuxFunction 
open import choiceSetU
open Process∞  
open Process+

STOP+ : (i : Size) → (c : Choice) →  Process+ i c
STOP+ i c =  process+ ∅' efq efq ∅' efq ∅' efq "STOP"

STOP : (i : Size) → (c : Choice) → Process i c
STOP i c = node (process+ ∅' efq efq ∅' efq ∅' efq "STOP")




SKIP+ : {i : Size} → {c : Choice} → (a : ChoiceSet c)
        → Process+ i c
SKIP+ a 
   = process+ ∅' efq efq ∅' efq ⊤' (λ _ → a)
              ("SKIP(" ++s choice2Str a ++s ")")


SKIP : {i : Size} → {c : Choice} → (a : ChoiceSet c)
        → Process i c
SKIP a = node (SKIP+ a )


TERMINATE : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process i c
TERMINATE a = terminate a

TERMINATE∞ : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process∞ i c
forcep (TERMINATE∞ a)    = TERMINATE a
Str∞   (TERMINATE∞ a)    = "terminate(" ++s choice2Str a ++s ")"


SKIPL+ : {i : Size} → {c : Choice} → List (ChoiceSet c) → Process+ i c
SKIPL+  l = process+ ∅' efq efq ∅' efq (fin (length l)) (nth l) "SKIPL ???"
