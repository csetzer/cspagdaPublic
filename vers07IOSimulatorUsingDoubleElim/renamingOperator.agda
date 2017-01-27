module renamingOperator where

open import Size
open import process
open import choiceSetU
open import choiceAuxFunction
open import dataAuxFunction
open import auxData
open import label
open import Data.String renaming (_++_ to _++s_)
open Process+
open Process∞
open import showLabelP





mutual 
   Rename∞ : (i : Size) → {c : Choice} → (f : Label → Label) → Process∞ i (ChoiceSet c) → Process∞ i (ChoiceSet c)
   forcep (Rename∞ i f a) j = Rename j f (forcep a j)
   
   Rename : (i : Size) → {c : Choice} → (f : Label → Label) → Process i (ChoiceSet c)  → Process i (ChoiceSet c)
   Rename i {c} f (node P) = node (Rename+ i f P)
   Rename i f (terminate x) = terminate x

   Rename+ : (i : Size) → {c : Choice} → (f : Label → Label) → Process+ i (ChoiceSet c)  → Process+ i (ChoiceSet c)
   E   (Rename+ i f P)        = (E P) 
   Lab (Rename+ i f P) c      = f (Lab P c)  --Check 
   PE  (Rename+ i f P) c      = PE P c
   I   (Rename+ i f P)        = I P  
   PI  (Rename+ i f P) c      = PI P c 
   Str (Rename+ i f P)        = "(" ++s Str P ++s  ")" ++s (labelLabelFunToString f)


