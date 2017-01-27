module indTr where

open import Size 
open import Data.List
open import Data.Product
open import Data.Maybe
open import label
open import Data.Product
open import process
open Process∞
open Process
open Process'
open import choiceSetU


data Tr' {i : Size} {c : Choice } : (l : List Label) → Maybe (ChoiceSet c) → (P : Process' i c) → Set where 
     empty : {P : Process' i c} → Tr' [] nothing P
     extchoice : {P  : Process' i c}
         → (l : List Label)
         → (tick : Maybe (ChoiceSet c))
         → (x : ChoiceSet (E P))
         → ({j : Size< i} → Tr' {j} l tick (PE P x))
         → Tr' (Lab P x ∷ l) tick P
     intchoice : {P  : Process' i c}
         → (l : List Label)
         → (tick : Maybe (ChoiceSet c))
         → (x : ChoiceSet (I P))
         → ({j : Size< i} → Tr' {j} l tick (PI P x))
         → Tr' l tick P
     terchoice : {P  : Process' i c}
         → (x : ChoiceSet (T P))
         → Tr' [] (just (PT P x)) P

     



mutual   
    data Tr {i : Size} {c : Choice } : (l : List Label) → Maybe (ChoiceSet c) → (P : Process i c) → Set where 
     empty : {P : Process i c} → Tr [] nothing P
     extchoice : {P  : Process i c}
         → (l : List Label)
         → (tick : Maybe (ChoiceSet c))
         → (x : ChoiceSet (E P))
         → Tr∞  l tick (PE P x)
         → Tr (Lab P x ∷ l) tick P
     intchoice : {P  : Process i c}
         → (l : List Label)
         → (tick : Maybe (ChoiceSet c))
         → (x : ChoiceSet (I P))
         → Tr∞ l tick (PI P x)
         → Tr l tick P
     terchoice : {P  : Process i c}
         → (x : ChoiceSet (T P))
         → Tr [] (just (PT P x)) P



    record Tr∞  {i : Size} {c : Choice} (l : List Label) (tick : Maybe (ChoiceSet c)) (P : Process∞ i c) :  Set  where
      coinductive
      field
       forcet :  {j : Size< i} → Tr {j} l tick (forcep P) 




Ref : {i : Size} → {c₀  : Choice} → (P : Process i c₀) → (Q : Process i c₀)  → Set 
Ref {i} {c₀} P Q  = (l : List Label) → (m₀ : Maybe (ChoiceSet c₀)) → Tr l m₀ P → Tr l m₀ Q 

_⊑_ = Ref




RefTr : {i : Size} → {c₀  c₁ : Choice} → (P : Process i c₀) → (Q : Process i c₁)  → Set 
RefTr {i} {c₀} {c₁} P Q  = (l : List Label) → (m₀ : Maybe (ChoiceSet c₀)) → (m₁ : Maybe (ChoiceSet c₁)) 
      → Tr l m₀ P → Tr l m₁ Q 
_⊑Tr_ = RefTr

<<<<<<< HEAD
RefTr∞ : {i : Size} → {c₀  c₁ : Choice} → (P : Process∞ i c₀) → (Q : Process∞ i c₁)  → Set 
RefTr∞ {i} {c₀} {c₁} P Q  = (l : List Label) → (m₀ : Maybe (ChoiceSet c₀)) → (m₁ : Maybe (ChoiceSet c₁)) 
      → Tr∞ l m₀ P → Tr∞ l m₁ Q 
_⊑Tr∞_ = RefTr∞
=======
infix 3 _⊑Tr_ 

_≡Tr_ : {i : Size} → {c₀  c₁ : Choice} → (P : Process i c₀) → (Q : Process i c₁)  → Set 
P ≡Tr Q =  P ⊑Tr Q ×  Q ⊑Tr P

>>>>>>> 9c6852a0f2c707ab155fc63e54f3fc02b39238e6


Ref∞ : {i : Size} → {c : Choice} →  (P : Process∞ i c) (Q : Process∞ i c)  → Set 
Ref∞ {i} {c} P  Q  = (l : List Label) → (m : Maybe (ChoiceSet c)) → Tr∞  l m P → Tr∞ l m Q
_⊑∞_ = Ref∞




{- needs to be changed *** -}
Ref' : {i : Size} → {c₀ c₁ : Choice} →  (m₀ : Maybe (ChoiceSet c₀)) → (m₁ : Maybe (ChoiceSet c₁)) → (P : Process' i c₀) (Q : Process' i c₁)  → Set 
Ref' {i} {c₀} {c₁} m₀ m₁ P Q  = (l : List Label) → Tr' l m₀ P → Tr' l m₁ Q 

_⊑'_ = Ref'


------------------------------------------------------------justTry---------------------------------------------------------------


data TrN' {i : Size} {c : Choice } : (l : List Label) → (P : Process' i c) → Set where 
     empty : {P : Process' i c} → TrN' [] P
     extchoice : {P  : Process' i c}
         → (l : List Label)
         → (x : ChoiceSet (E P))
         → ({j : Size< i} → TrN' {j} l (PE P x))
         → TrN' (Lab P x ∷ l)  P
     intchoice : {P  : Process' i c}
         → (l : List Label)
         → (x : ChoiceSet (I P))
         → ({j : Size< i} → TrN' {j} l (PI P x))
         → TrN' l P
     terchoice : {P  : Process' i c}
         → (x : ChoiceSet (T P))
         → TrN' [] P



RefN' : {i : Size} → {c₀ c₁ : Choice} → (P : Process' i c₀) (Q : Process' i c₁)  → Set 
RefN' {i} {c₀} {c₁} P Q  = (l : List Label) → TrN' l P → TrN' l  Q 

_⊑N'_ = Ref'


_≡_ : {i : Size} → {c : Choice} → (P : Process i c) → (Q : Process i c) → Set 
P ≡ Q =  (P ⊑ Q) ×  (Q ⊑ P)

infix 3 _≡_

_≡Tr_ : {i : Size} → {c₀ c₁ : Choice} → (P : Process i c₀) → (Q : Process i c₁) → Set 
P ≡Tr Q =  P ⊑Tr Q ×  Q ⊑Tr P

infix 3 _≡Tr_
