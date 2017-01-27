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
open import syntaxOfCSPAgda


STOP+ : {i : Size} → {c : Choice} →  Process+ i c
STOP+ =  process+ ∅' efq efq ∅' efq ∅' efq STOP'' 

STOP : {i : Size} → {c : Choice} → Process i c
STOP = node (process+ ∅' efq efq ∅' efq ∅' efq STOP'')



STOP' : {i : Size} → {c : Choice} → Process i c
STOP' = node STOP+ 

STOP∞  : {i : Size} → {c : Choice} → Process∞ i c
STOP∞ = delay STOP'





{-Used one-}
SKIP+ : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process+ i c
SKIP+ a = process+ ∅' efq efq ∅' efq ⊤' (λ _ → a) (SKIP'' a)

SKIP : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process i c
SKIP a = node (SKIP+ a )


-- not finalised but not used elsewhere so insufficent string can be ignored
MSKIP+ : {i : Size} → {c : Choice} → (t : Choice) → (f : ChoiceSet t → ChoiceSet c) → Process+ i c
MSKIP+ t f = process+ ∅' efq efq ∅' efq t f (MSKIP' f) -- "MSKIP ???"


-- not finalised but not used elsewhere so insufficent string can be ignored
MSKIP : {i : Size} → {c : Choice} → (t : Choice) → (f : ChoiceSet t → ChoiceSet c) → Process i c
MSKIP t f = node (MSKIP+ t f )

-- not finalised but not used elsewhere so insufficent string can be ignored
MSKIPi : (i : Size) → (c : Choice) → (t : Choice) → (f : ChoiceSet t → ChoiceSet c) → Process i c
MSKIPi i c  = MSKIP {i} {c}


TERMINATE : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process i c
TERMINATE a = terminate a

TERMINATE∞ : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process∞ i c
forcep (TERMINATE∞ a) = TERMINATE a

Syn∞   (TERMINATE∞ a) = terminate' a -- "terminate(" ++s choice2Str a ++s ")"





-- not finalised but not used elsewhere so insufficent string can be ignored
SKIPL+ : {i : Size} → {c : Choice} → List (ChoiceSet c) → Process+ i c
SKIPL+ {i} {c} l = process+ ∅' efq efq ∅' efq (fin (length l)) (nth l) (SKIPL' l)
