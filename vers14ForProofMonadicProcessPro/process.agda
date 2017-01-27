module process where 

open import choiceSetU
open import label
open import Size
open import Data.String renaming (_++_ to _++s_)


mutual 
  record  Process∞ (i : Size) (c : Choice) : Set where
    coinductive
    field
      forcep : {j : Size< i} → Process j c 
      Str∞   : String

  data Process (i : Size)  (c : Choice) : Set where
    terminate  : ChoiceSet  c    → Process i c
    node       : Process+   i c  → Process i c

  record Process+ (i : Size) (c : Choice) : Set where
    constructor process+
    coinductive
    field
      E     :  Choice
      Lab   :  ChoiceSet  E  →  Label
      PE    :  ChoiceSet  E  →  Process∞  i  c
      I     :  Choice
      PI    :  ChoiceSet  I  →  Process∞  i  c
      T     :  Choice
      PT    :  ChoiceSet  T  →  ChoiceSet c
      Str+  :  String


open Process∞ public 
open Process+ public 


Str : {i : Size} → {c : Choice} → Process i c → String
Str (terminate a) = "terminate("++s choice2Str a ++s")"
Str (node P)      = Str+ P 


delay : {i : Size} →  {c : Choice} → Process i c
        → Process∞ (↑ i) c
forcep (delay  P)   = P
Str∞   (delay  P)   = Str P

delayi : (i : Size) →  {c : Choice} → Process i c
        → Process∞ (↑ i) c
forcep (delayi  i P)   = P
Str∞   (delayi  i P)   = Str P

