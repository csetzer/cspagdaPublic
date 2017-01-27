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




STOP+ : (i : Size) → (c : Choice) →  Process+ (↑ i) (ChoiceSet c)
STOP+ i c =  process+ empty efq efq empty efq empty efq "STOP"

STOP : (i : Size) → (c : Choice) → Process (↑ i) (ChoiceSet c)
STOP i c = node (STOP+ i c )

Stop :  {i : Size} → {c : Choice} →  Process (↑ i) (ChoiceSet c)
Stop {i} {c} = STOP i c



{-Used one-}
SKIP+ : (i : Size) → (c : Choice) → (a : ChoiceSet c) → Process+ (↑ i) (ChoiceSet c)
SKIP+ i c a = process+ empty efq efq empty efq unitc (λ _ → a) ("SKIP(" ++s choice2String c a ++s ")")
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


SKIP : (i : Size) → (c : Choice) → (a : ChoiceSet c) → Process (↑ i) (ChoiceSet c)
SKIP i c a = node (SKIP+ i c a )

Skip : {i : Size} → {c : Choice} → ChoiceSet c → Process (↑ i) (ChoiceSet c)
Skip {i} {c}  = SKIP i c



-- not finalised but not used elsewhere so insufficent string can be ignored
MSKIP+ : (i : Size) → (A : Set) → (t : Choice) → (f : ChoiceSet t → A) → Process+ (↑ i) A
MSKIP+ i A t f = process+ empty efq efq empty efq t f "MSKIP ???"


-- not finalised but not used elsewhere so insufficent string can be ignored
MSKIP : (i : Size) → (A : Set) → (t : Choice) → (f : ChoiceSet t → A) → Process (↑ i) A
MSKIP i c t f = node (MSKIP+ i c t f )

-- not finalised but not used elsewhere so insufficent string can be ignored
MSkip : {i : Size} → {A : Set} → (t : Choice) → (f : ChoiceSet t → A) → Process (↑ i) A
MSkip {i} {c}  = MSKIP i c


-- not finalised but not used elsewhere so insufficent string can be ignored
TERMINATE : {i : Size} → {A : Set} → (a : A) → Process i A
TERMINATE a = terminate a


-- not finalised but not used elsewhere so insufficent string can be ignored
SKIPL+ : {i : Size} → {A : Set} → List A → Process+ (↑ i) A
SKIPL+ {i} {A} l = process+ empty efq efq empty efq (fin (length l)) (nth l) "SKIPL ???"
