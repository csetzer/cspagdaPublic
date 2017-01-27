module process where 

open import choiceSetU
open import label
open import Size


record Process' (i : Size) (c : Choice) : Set where
  constructor process+
  coinductive
  field
    E     :  Choice
    Lab   :  ChoiceSet  E  →  Label
    PE    :  {j : Size< i} → ChoiceSet  E  →  Process'  j  c
    I     :  Choice
    PI    :  {j : Size< i} → ChoiceSet  I  →  Process'  i  c 
    T     :  Choice
    PT    :  ChoiceSet  T  →  ChoiceSet c




mutual 
  record  Process∞ (i : Size) (c : Choice) : Set where
    coinductive
    field
      forcep : {j : Size< i} → Process j c 


  record Process (i : Size) (c : Choice) : Set where
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



open Process∞
open Process
open Process'



delay : {i : Size} →  {c : Choice} → Process i c
        → Process∞ (↑ i) c
forcep (delay  P)   = P


delayi : (i : Size) →  {c : Choice} → Process i c
        → Process∞ (↑ i) c
forcep (delayi  i P)   = P
