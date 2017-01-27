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



STOP+ : {i : Size} → {c : Choice} →  Process+ i c
STOP+ =  process+ ∅' efq efq ∅' efq ∅' efq "STOP"

STOP : {i : Size} → {c : Choice} → Process i c
STOP = node (process+ ∅' efq efq ∅' efq ∅' efq "STOP")

{- better version of STOP+ but not in paper -}

STOP' : {i : Size} → {c : Choice} → Process i c
STOP' = node STOP+ 

STOP∞  : {i : Size} → {c : Choice} → Process∞ i c
STOP∞ = delay STOP'



{-
recStr : {c₀ : Choice} → (ChoiceSet c₀ → String) → ChoiceSet c₀ → String
recStr f a = "rec(" ++s choice2Str2Str f ++s "," ++s choice2Str a ++s ")"
-}

{-
Stop :  {i : Size} → {c : Choice} →  Process i c
Stop {i} {c} = STOP i c
-}



{-Used one-}
SKIP+ : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process+ i c
SKIP+ a = process+ ∅' efq efq ∅' efq ⊤' (λ _ → a) ("SKIP(" ++s choice2Str a ++s ")")
{-
E   (SKIP+ i c a)    = fin 0
Lab (SKIP+ i c a) ()
PE  (SKIP+ i c a) ()
I   (SKIP+ i c a)    = fin 0
PI  (SKIP+ i c a) ()
T   (SKIP+ i c a)    = fin 1
PT  (SKIP+ i c a) x  =  a
Str (SKIP+ i c a)    = "SKIP"
-}


SKIP : {i : Size} → {c : Choice} → (a : ChoiceSet c) → Process i c
SKIP a = node (SKIP+ a )


{-
Skip : {i : Size} → {c : Choice} → ChoiceSet c → Process i c
Skip {i} {c}  = SKIP i c
-}


-- not finalised but not used elsewhere so insufficent string can be ignored
MSKIP+ : {i : Size} → {c : Choice} → (t : Choice) → (f : ChoiceSet t → ChoiceSet c) → Process+ i c
MSKIP+ t f = process+ ∅' efq efq ∅' efq t f "MSKIP ???"


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
Str∞   (TERMINATE∞ a) = "terminate(" ++s choice2Str a ++s ")"




-- not finalised but not used elsewhere so insufficent string can be ignored
SKIPL+ : {i : Size} → {c : Choice} → List (ChoiceSet c) → Process+ i c
SKIPL+ {i} {c} l = process+ ∅' efq efq ∅' efq (fin (length l)) (nth l) "SKIPL ???"
