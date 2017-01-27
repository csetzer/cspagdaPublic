module div where 

open import Size
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import Data.List
open import process
open import auxData
open import dataAuxFunction 
open import choiceSetU
open Process∞  
open Process+

mutual
  DIV∞  : {i : Size} → {c : Choice} → Process∞ i c
  forcep  DIV∞   = node (process+ ∅' efq efq ⊤'
                        (λ _ → DIV∞) ∅' efq "DIV")
  Str∞    DIV∞   =  "DIV"

