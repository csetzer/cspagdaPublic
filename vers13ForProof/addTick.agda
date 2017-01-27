module addTick where

open import Size


open import Data.Sum
open import label
open import process
open import choiceSetU
open import dataAuxFunction
open import renamingResult
open import Data.Fin
open Process∞
open Process

if_then_else_ : {A : Set} → ChoiceSet bool → A → A → A
if zero then a else b = a
if suc zero then a else b = b
if suc (suc ()) then a else b



2-✓+ : ∀ {i} → {c₀ c₁ : Choice} → (a : ChoiceSet c₀) 
             → (a' : ChoiceSet c₁) → Process i (c₀ ⊎' c₁)
2-✓+ a a' = process+ ∅' efq efq ∅' efq bool (λ b → if b then (inj₁ a) else (inj₂ a')) 
  


2-✓+' : ∀ {i} → {c₀ c₁ : Choice} → (a : ChoiceSet c₀) 
             → (a' : ChoiceSet c₁) → Process i (c₀ ⊎' c₁)
E     (2-✓+' a a')      =  ∅' 
Lab   (2-✓+' a a')  ()
PE    (2-✓+' a a')  ()
I     (2-✓+' a a')      =  ∅'
PI    (2-✓+' a a')  ()
T     (2-✓+' a a')      =  fin 2
PT    (2-✓+' a a')  zero = inj₁ a
PT    (2-✓+' a a') (suc zero) = inj₂ a'
PT    (2-✓+' a a') (suc (suc ()))



2-✓ :  ∀ {i} → {c₀ c₁ : Choice} → (a : ChoiceSet c₀) 
             → (a' : ChoiceSet c₁) → Process i (c₀ ⊎' c₁)

2-✓ a a' = 2-✓+ a a'



unifyA⊎A : {A : Set} → A ⊎ A → A
unifyA⊎A (inj₁ a) = a
unifyA⊎A (inj₂ a) = a



mutual
  add✓∞ : ∀ {i} → {c : Choice} → (a : ChoiceSet c) 
          → Process∞ i c → Process∞  i c

  forcep (add✓∞  a P) = add✓ a (forcep P)
  

  add✓  : ∀ {i} → {c : Choice} → (a : ChoiceSet c) 
             → Process i c → Process i c
  add✓  a P       = add✓+ a P



  add✓+ : ∀ {i} → {c : Choice} → (a : ChoiceSet c) 
                → Process i c → Process i c 
  E    (add✓+ a P)    = E P
  Lab  (add✓+ a P)    = Lab P 
  PE   (add✓+ a P) s  = add✓∞ a (PE P s)
  I    (add✓+ a P)    = I P
  PI   (add✓+ a P) s  = add✓∞ a (PI P s)
  T    (add✓+ a P)    = ⊤'  ⊎'  T P 
  PT   (add✓+ a P) (inj₁ _) = a
  PT   (add✓+ a P) (inj₂ c) = PT P c





mutual
  addTimed✓∞ : ∀ {i} → {c : Choice} → (a : ChoiceSet c) → Process∞ i c → Process∞  i c
  forcep (addTimed✓∞  a P) = addTimed✓ a (forcep P)
  

  addTimed✓  : ∀ {i} → {c : Choice} → (a : ChoiceSet c) → Process i c → Process i c
  addTimed✓  a  P       = addTimed✓+ a P


  addTimed✓+ : ∀ {i} → {c : Choice} → (a : ChoiceSet c) 
                  → Process i c 
                  → Process i c 
  E    (addTimed✓+ a P)    = E P
  Lab  (addTimed✓+ a P)    = Lab P 
  PE   (addTimed✓+ a P) s  = PE P s
  I    (addTimed✓+ a P)    = I P
  PI   (addTimed✓+ a P) s  = addTimed✓∞ a (PI P s)
  T    (addTimed✓+ a P)    = ⊤'  ⊎'  T P 
  PT   (addTimed✓+ a P) (inj₁ _) = a
  PT   (addTimed✓+ a P) (inj₂ c) = PT P c



