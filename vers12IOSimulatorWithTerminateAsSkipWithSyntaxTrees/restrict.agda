module restrict where


open import Data.Bool renaming (T to True)
open import Data.Sum
open import Data.Sum
open import Data.String renaming (_++_ to _++s_)
open import Data.String.Base 
open import Size 
open import process 
open Process∞
open Process+
open import label
open import showLabelP
open import choiceSetU
open import dataAuxFunction
open import auxData
open import CSPAgdaSyntax

-- restriction of external labels to those for which a function is true

-- ↾  is input as \uprightharpoon

mutual
  _↾∞_ : {i : Size} → {c : Choice} → Process∞ i c
             → (A : Label → Bool)  → Process∞ i c
  forcep (P ↾∞ A) = (forcep P) ↾ A 
  Syn∞   (P ↾∞ A) = (Syn∞ P) ↾' A 

  _↾_ : {i : Size} → {c : Choice} → Process i c
             → (A : Label → Bool)  → Process i c
  terminate a ↾ A  = terminate a
  node P      ↾ A  = node (P ↾+ A)


  _↾+_ : {i : Size} → {c : Choice} → Process+ i c
          → (A : Label → Bool)  → Process+ i c
  E    (P ↾+ A)         =   subset' (E P) (A ∘ (Lab P))
  Lab  (P ↾+ A) (sub c p) = Lab P c
  PE   (P ↾+ A) (sub c p) = PE P c ↾∞ A
  I    (P ↾+ A)           = I P 
  PI   (P ↾+ A) c         = PI P c ↾∞ A
  T    (P ↾+ A)           = T P
  PT   (P ↾+ A) c         = PT P c
  Syn+ (P ↾+ A)           = Syn+ P ↾' A
