module preFix where

open import Size
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import label
open import process
open import choiceSetU
open import showFunction
open import dataAuxFunction
open import showLabelP
open Process∞
open Process+

_⟶Str_ : Label → String → String
l ⟶Str s = "(" ++s showLabel l ++s " ⟶  " ++s s ++s ")"

_⟶+_ : {i : Size} → {c : Choice} → Label → Process∞ i c → Process+ i c
l ⟶+ P   = process+ ⊤' (λ _ →  l) (λ _ → P) ∅' efq ∅' efq 
                     (l ⟶Str Str∞ P )


_⟶_ : {i : Size} → {c : Choice} → Label → Process∞ i c → Process i c
l ⟶ P = node (l ⟶+ P )


{- Nicer looking version, use in library instead of _⟶+_
   but not in paper -}
_⟶+'_ : {i : Size} → {c : Choice} → Label → Process∞ i c → Process+ i c
E    (l ⟶+' P)   = ⊤'
Lab  (l ⟶+' P) c = l
PE   (l ⟶+' P) c = P
I    (l ⟶+' P)   = ∅'
PI   (l ⟶+' P) ()
T    (l ⟶+' P)   = ∅'
PT   (l ⟶+' P) ()
Str+ (l ⟶+' P)   = l ⟶Str Str∞ P 

_⟶++_ : {i : Size} → {c : Choice} → Label → Process+ i c → Process+ i c
l ⟶++ P = l ⟶+ (delay (node P) )

_⟶p+_ : {i : Size} → {c : Choice} → Label → Process i c → Process+ i c
l ⟶p+ P = l ⟶+ (delay P )

_⟶pp_ : {i : Size} → {c : Choice} → Label → Process i c → Process i c
l ⟶pp P = node (l ⟶+ (delay P ))

_⟶p∞_ : {i : Size} → {c : Choice} → Label → Process i c → Process∞ i c
forcep (l ⟶p∞ P)  = l ⟶pp P 
Str∞   (l ⟶p∞ P)  = l ⟶Str Str P
