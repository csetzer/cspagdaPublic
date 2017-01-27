module traceEquivalence where

open import Size 
open import Data.List
open import Data.Product
open import Data.Maybe
open import label
open import process
open import choiceSetU
open import TraceWithoutSize
open import RefWithoutSize

_≡_ : {c₀ : Choice} → (P Q : Process ∞ c₀) → Set 
P ≡ Q =  P ⊑ Q ×  Q ⊑ P

_≡∞_ : {c₀ : Choice} → (P Q : Process∞ ∞ c₀) → Set 
P ≡∞ Q =  P ⊑∞ Q ×  Q ⊑∞ P

_≡+_ : {c₀ : Choice} → (P Q : Process+ ∞ c₀) → Set 
P ≡+ Q =  P ⊑+ Q ×  Q ⊑+ P

