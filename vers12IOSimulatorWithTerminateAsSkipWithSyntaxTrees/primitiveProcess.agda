module primitiveProcess where 

open import Size
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import Data.List
open import process
open import auxData
open import dataAuxFunction 
open import choiceSetU
open Process∞  
open Process+
open import CSPAgdaSyntax


STOP+ : {i : Size} → {c : Choice} →  Process+ i c
STOP+  =  process+ ∅' efq efq ∅' efq ∅' efq  STOP''


STOP : {i : Size} → {c : Choice} → Process i c
STOP = node STOP+ 

STOP∞  : {i : Size} → {c : Choice} → Process∞ i c
STOP∞ = delay STOP




MSKIP+ : (i : Size) → (c : Choice) → (t : Choice) → (f : ChoiceSet t → ChoiceSet c) → Process+ i c
MSKIP+ i c t f = process+ ∅' efq efq ∅' efq t f (MSKIP' f) 



MSKIP : (i : Size) → (c : Choice) → (t : Choice) → (f : ChoiceSet t → ChoiceSet c) → Process i c
MSKIP i c t f = node (MSKIP+ i c t f )


MSkip : {i : Size} → {c : Choice} → (t : Choice) → (f : ChoiceSet t → ChoiceSet c) → Process i c
MSkip {i} {c}  = MSKIP i c

SKIP+ : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process+ i c
SKIP+ a = process+ ∅' efq efq ∅' efq ⊤' (λ _ → a) (SKIP'' a) 


SKIP : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process i c
SKIP a = node (SKIP+ a )

TERMINATE : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process i c
TERMINATE a = terminate a

TERMINATE∞ : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process∞ i c
forcep (TERMINATE∞ a)   = TERMINATE a
Syn∞   (TERMINATE∞ a)   = terminate' a

SKIPL+ : {i : Size} → {c : Choice} → List (ChoiceSet c) → Process+ i c
SKIPL+ {i} {c} l = process+ ∅' efq efq ∅' efq (fin (length l)) (nth l) (SKIPL' l)
