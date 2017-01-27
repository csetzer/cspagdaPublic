module refinement where

open import Size 
open import Data.List
open import Data.Product
open import Data.Maybe
open import label
open import process
open import choiceSetU
open import indTr

_⊑_ : {i : Size} {c : Choice} (P : Process i c) (Q : Process i c) → Set 
_⊑_ {i} {c} P Q  = (l : List Label) → (m : Maybe (ChoiceSet c)) → Tr l m Q → Tr l m P 
Ref = _⊑_ 

_⊑∞_ : {i : Size} → {c : Choice} → (P : Process∞ i c) (Q : Process∞ i c) → Set 
_⊑∞_ {i} {c} P Q = (l : List Label) → (m : Maybe (ChoiceSet c)) → Tr∞ l m Q → Tr∞ l m P
Ref∞ = _⊑∞_

_⊑+_ : {i : Size} {c : Choice} (P : Process+ i c) (Q : Process+ i c)  → Set 
_⊑+_ {i} {c} P Q = (l : List Label) → (m : Maybe (ChoiceSet c)) → Tr+ l m Q → Tr+ l m P
Ref+ = _⊑+_






_⊑ᵣ_ : {i : Size} {c c₁ : Choice} (P : Process i c) (Q : Process i c₁) → Set 
_⊑ᵣ_ {i} {c} {c₁} P Q  = (l : List Label) → (m : Maybe (ChoiceSet c)) → (m₁ : Maybe (ChoiceSet c₁)) → Tr l m₁ Q → Tr l m P 
Refᵣ = _⊑ᵣ_ 

_⊑∞ᵣ_ : {i : Size} {c c₁ : Choice} (P : Process∞ i c) (Q : Process∞ i c₁) → Set 
_⊑∞ᵣ_ {i} {c} {c₁} P Q = (l : List Label) → (m : Maybe (ChoiceSet c)) → (m₁ : Maybe (ChoiceSet c₁)) → Tr∞ l m₁ Q → Tr∞ l m P
Ref∞ᵣ = _⊑∞ᵣ_

_⊑+ᵣ_ : {i : Size} {c c₁ : Choice} (P : Process+ i c) (Q : Process+ i c₁)  → Set 
_⊑+ᵣ_ {i} {c} {c₁} P Q = (l : List Label) → (m : Maybe (ChoiceSet c)) → (m₁ : Maybe (ChoiceSet c₁)) → Tr+ l m₁ Q → Tr+ l m P
Ref+ᵣ = _⊑+ᵣ_

