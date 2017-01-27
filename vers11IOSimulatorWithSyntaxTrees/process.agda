module process where 

open import Data.String renaming (_++_ to _++s_)
open import choiceSetU
open import label
open import Size
open import Data.String
open import syntaxOfCSPAgda

mutual 
  record  Process∞ (i : Size) (c : Choice) : Set where
    coinductive
    field
      forcep : {j : Size< i} → Process j c 
      Syn∞   : Syntax

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
      Syn+  : Syntax
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
       →  (Syn+  : Syntax)
       →  Process+ i c  
E    (process++ E Lab PE I PI T PT Syn+) = E
Lab  (process++ E Lab PE I PI T PT Syn+) = Lab
PE   (process++ E Lab PE I PI T PT Syn+) = PE
I    (process++ E Lab PE I PI T PT Syn+) = I
PI   (process++ E Lab PE I PI T PT Syn+) = PI
T    (process++ E Lab PE I PI T PT Syn+) = T
PT   (process++ E Lab PE I PI T PT Syn+) = PT
Syn+ (process++ E Lab PE I PI T PT Syn+) = Syn+

Syn : {i : Size} → {c : Choice} → Process i c → Syntax
Syn (terminate a) = terminate' a -- "terminate(" ++s choice2Str a ++s ")"
Syn (node P)      = Syn+ P 


delay : {i : Size} →  {c : Choice} → Process i c
        → Process∞ (↑ i) c
forcep (delay  P) = P
Syn∞   (delay  P) = Syn P

terminate∞  : {i : Size} →  {c : Choice} → ChoiceSet c → Process∞  i c
terminate∞  a = delay (terminate a)

delayi : (i : Size) →  {c : Choice} → Process i c
        → Process∞ (↑ i) c
forcep (delayi  i P) = P
Syn∞   (delayi  i P) = Syn P
