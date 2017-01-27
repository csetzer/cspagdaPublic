module renamingOperator where

open import Size
open import process
open ∞Process
open import choiceSetU
open import choiceAuxFunction
open import dataAuxFunction
open import auxData
open import label
open import Data.String renaming (_++_ to _++s_)
open import showFunction
open import choiceSetU


mutual 
   Rename : (i : Size) → {c : Choice} → (f : Label → Label) → ∞Process i (ChoiceSet c) → ∞Process i (ChoiceSet c)
   force (Rename i f a) j = Rename' j f (force a j)
   
   Rename' : (i : Size) → {c : Choice} → (f : Label → Label) → Process i (ChoiceSet c)  → Process i (ChoiceSet c)
   Rename' i f (node E Lab PE I PI Stat) = node E (f ∘ Lab) (λ x → PE x ) I (λ x → PI x) {!!}
   Rename' i f (terminate x) = terminate x
