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
      Str   : String
open Process∞
open Process+


delay : (i : Size) →  {A : Set} → Process i A  → Process∞ (↑ i) A 
forcep (delay i p) j = p
