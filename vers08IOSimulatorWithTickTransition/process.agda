module process where 

open import choiceSetU
open import label
open import Size
open import Data.String


mutual 
  record  Process∞ (i : Size) (A : Set) : Set where
    coinductive
    field
      forcep : (j : Size< i) → Process j A 

  data Process (i : Size)  (A : Set) : Set where
    terminate : A → Process i A
    node      : Process+ i A → Process i A


  record Process+ (i : Size) (A : Set) : Set where
    coinductive
    field
      E     : Choice
      Lab   : ChoiceSet E → Label
      PE    : ChoiceSet E →  Process∞ i A
      I     : Choice
      PI    : ChoiceSet I → Process∞ i A
      T     : Choice
      PT    : ChoiceSet T → A
      Str   : String
open Process∞
open Process+

process+ : {i : Size} → {A : Set} 
       →  (E     : Choice)
       →  (Lab : ChoiceSet E → Label)
       →  (PE    : ChoiceSet E →  Process∞ i A)
       →  (I     : Choice)
       →  (PI    : ChoiceSet I → Process∞ i A)
       →  (T     : Choice)
       →  (PT    : ChoiceSet T → A)
       →  (Str   : String)
       →  Process+ i A
E   (process+ {i} {A} E Lab PE I PI T PT Str) = E
Lab (process+ {i} {A} E Lab PE I PI T PT Str) = Lab
PE  (process+ {i} {A} E Lab PE I PI T PT Str) = PE
I   (process+ {i} {A} E Lab PE I PI T PT Str) = I
PI  (process+ {i} {A} E Lab PE I PI T PT Str) = PI
T   (process+ {i} {A} E Lab PE I PI T PT Str) = T
PT  (process+ {i} {A} E Lab PE I PI T PT Str) = PT
Str (process+ {i} {A} E Lab PE I PI T PT Str) = Str


delay : (i : Size) →  {A : Set} → Process i A  → Process∞ (↑ i) A 
forcep (delay i p) j = p
