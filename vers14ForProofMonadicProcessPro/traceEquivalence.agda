module traceEquivalence where

open import Size 
open import Data.List
open import Data.Product
open import Data.Maybe
open import label
open import process
open import choiceSetU
open import indTr
open import refinement

_≡_ : {i : Size} → {c₀ : Choice} → (P Q : Process i c₀) → Set 
P ≡ Q =  P ⊑ Q ×  Q ⊑ P

_≡∞_ : {i : Size} → {c₀ : Choice} → (P Q : Process∞ i c₀) → Set 
P ≡∞ Q =  P ⊑∞ Q ×  Q ⊑∞ P

_≡+_ : {i : Size} → {c₀ : Choice} → (P Q : Process+ i c₀) → Set 
P ≡+ Q =  P ⊑+ Q ×  Q ⊑+ P

