module process where 

open import Data.String renaming (_++_ to _++s_)
open import choiceSetU
open import label
open import Size
open import Data.String


mutual 
  record  Process∞ (i : Size) (c : Choice) : Set where
    coinductive
    field
      forcep : {j : Size< i} → Process j c 
      Str∞   : String

  data Process (i : Size)  (c : Choice) : Set where
    terminate : ChoiceSet c → Process i c
    node      : Process+ i c → Process i c


  record Process+ (i : Size) (c : Choice) : Set where
    constructor process+
    coinductive
    field
      E     : Choice
      Lab   : ChoiceSet E → Label
      PE    : ChoiceSet E →  Process∞ i c
      I     : Choice
      PI    : ChoiceSet I → Process∞ i c
      T     : Choice
      PT    : ChoiceSet T → ChoiceSet c
      Str+  : String
open Process∞
open Process+



{- Explicit version of process+ -}
process++ : {i : Size} → {c : Choice} 
       →  (E     : Choice)
       →  (Lab : ChoiceSet E → Label)
       →  (PE    : ChoiceSet E →  Process∞ i c)
       →  (I     : Choice)
       →  (PI    : ChoiceSet I → Process∞ i c)
       →  (T     : Choice)
       →  (PT    : ChoiceSet T → ChoiceSet c)
       →  (Str+  : String)
       →  Process+ i c  
E    (process++ E Lab PE I PI T PT Str+) = E
Lab  (process++ E Lab PE I PI T PT Str+) = Lab
PE   (process++ E Lab PE I PI T PT Str+) = PE
I    (process++ E Lab PE I PI T PT Str+) = I
PI   (process++ E Lab PE I PI T PT Str+) = PI
T    (process++ E Lab PE I PI T PT Str+) = T
PT   (process++ E Lab PE I PI T PT Str+) = PT
Str+ (process++ E Lab PE I PI T PT Str+) = Str+

Str : {i : Size} → {c : Choice} → Process i c → String
Str (terminate a) = "terminate(" ++s choice2Str a ++s ")"
Str (node P)      = Str+ P 


delay : {i : Size} →  {c : Choice} → Process i c
        → Process∞ (↑ i) c
forcep (delay  P) = P
Str∞   (delay  P) = Str P

terminate∞  : {i : Size} →  {c : Choice} → ChoiceSet c → Process∞  i c
terminate∞  a = delay (terminate a)

delayi : (i : Size) →  {c : Choice} → Process i c
        → Process∞ (↑ i) c
forcep (delayi  i P) = P
Str∞   (delayi  i P) = Str P



{-
postulate c      : Choice
postulate E'     : Choice
postulate Lab'   : ChoiceSet E' → Label
postulate PE'    : (i : Size) → ChoiceSet E' →  Process∞ i  c
postulate I'     : Choice
postulate PI'    : (i : Size) → ChoiceSet I' → Process∞ i  c
postulate T'     : Choice
postulate PT'    : ChoiceSet T' → ChoiceSet c
postulate Str+'  : String

test : ∀ i →  Process+ i c
test i = process+ {i} {c} E' Lab' (PE' i)  I' (PI' i) T' PT' Str+'
-}
