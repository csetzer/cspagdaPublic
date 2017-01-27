module addTick where

open import Size
open import Data.String renaming (_++_ to _++s_)
open import Data.Fin
open import Data.Sum
open import label
open import process
open import choiceSetU
open import showFunction
open import dataAuxFunction
open import showLabelP
open import renamingResult
open import internalChoice
open Process∞
open Process+

2-✓Str : {c₀ c₁ : Choice} → (a : ChoiceSet c₀) 
             → (a' : ChoiceSet c₁)  → String
2-✓Str a a' = "(2-✓ "++s choice2Str a ++s " " ++s choice2Str a' ++s ")"


2-✓+ : ∀ {i} → {c₀ c₁ : Choice} → (a : ChoiceSet c₀) 
             → (a' : ChoiceSet c₁) → Process+ i (c₀ ⊎' c₁)
2-✓+ a a' = process+ ∅' efq efq ∅' efq bool 
               (λ b → if b then (inj₁ a) else (inj₂ a')) 
               (2-✓Str a a')


2-✓+' : ∀ {i} → {c₀ c₁ : Choice} → (a : ChoiceSet c₀) 
             → (a' : ChoiceSet c₁) → Process+ i (c₀ ⊎' c₁)
E     (2-✓+' a a')      =  ∅' 
Lab   (2-✓+' a a')  ()
PE    (2-✓+' a a')  ()
I     (2-✓+' a a')      =  ∅'
PI    (2-✓+' a a')  ()
T     (2-✓+' a a')      =  fin 2
PT    (2-✓+' a a')  zero = inj₁ a
PT    (2-✓+' a a') (suc zero) = inj₂ a'
PT    (2-✓+' a a') (suc (suc ()))
Str+  (2-✓+' a a' )    =  "(2-✓ "++s choice2Str a ++s " " ++s choice2Str a' ++s ")"

2-✓ :  ∀ {i} → {c₀ c₁ : Choice} → (a : ChoiceSet c₀) 
             → (a' : ChoiceSet c₁) → Process i (c₀ ⊎' c₁)

2-✓ a a' = node (2-✓+ a a')


--defined 2-✓∞ for Idem proof

2-✓∞ :  ∀ {i} → {c₀ c₁ : Choice} → (a : ChoiceSet c₀) 
             → (a' : ChoiceSet c₁) → Process∞ i (c₀ ⊎' c₁)
forcep (2-✓∞ a a') =  (2-✓ a a')
Str∞ (2-✓∞ a a')   = 2-✓Str a a'


unifyA⊎A : {A : Set} → A ⊎ A → A
unifyA⊎A (inj₁ a) = a
unifyA⊎A (inj₂ a) = a


add✓Str : ∀ {c : Choice} → (a : ChoiceSet c) 
           → String → String
add✓Str a str = "(add✓ " ++s choice2Str a ++s " " ++s str ++s ")"


mutual
  add✓∞ : ∀ {i} → {c : Choice} → (a : ChoiceSet c) 
          → Process∞ i c → Process∞  i c

  forcep (add✓∞  a P) = add✓ a (forcep P)
  Str∞   (add✓∞  a P) = add✓Str a  (Str∞ P)

  add✓  : ∀ {i} → {c : Choice} → (a : ChoiceSet c) 
             → Process i c → Process i c
  add✓  a (terminate a') = fmap unifyA⊎A (2-✓ a a' )
  add✓  a (node P)       = node (add✓+ a P)



  add✓+ : ∀ {i} → {c : Choice} → (a : ChoiceSet c) 
                → Process+ i c → Process+ i c 
  E    (add✓+ a P)    = E P
  Lab  (add✓+ a P)    = Lab P 
  PE   (add✓+ a P) s  = add✓∞ a (PE P s)
  I    (add✓+ a P)    = I P
  PI   (add✓+ a P) s  = add✓∞ a (PI P s)
  T    (add✓+ a P)    = ⊤'  ⊎'  T P 
  PT   (add✓+ a P) (inj₁ _) = a
  PT   (add✓+ a P) (inj₂ c) = PT P c
  Str+ (add✓+  a P)  = add✓Str a  (Str+ P)



addTimed✓Str : {c : Choice} → (a : ChoiceSet c)  → String  → String
addTimed✓Str a str = "(addTimed✓ " ++s choice2Str a ++s " " ++s str ++s ")"


mutual
  addTimed✓∞ : ∀ {i} → {c : Choice} → (a : ChoiceSet c) → Process∞ i c → Process∞  i c
  forcep (addTimed✓∞  a P) = addTimed✓ a (forcep P)
  Str∞   (addTimed✓∞  a P) = addTimed✓Str a  (Str∞ P)

  addTimed✓  : ∀ {i} → {c : Choice} → (a : ChoiceSet c) → Process i c → Process i c
  addTimed✓  a (terminate a') = fmap unifyA⊎A (2-✓ a a' )
  addTimed✓  a (node P)       = node (addTimed✓+ a P)



  addTimed✓+ : ∀ {i} → {c : Choice} → (a : ChoiceSet c) 
                  → Process+ i c 
                  → Process+ i c 
  E    (addTimed✓+ a P)    = E P
  Lab  (addTimed✓+ a P)    = Lab P 
  PE   (addTimed✓+ a P) s  = PE P s
  I    (addTimed✓+ a P)    = I P
  PI   (addTimed✓+ a P) s  = addTimed✓∞ a (PI P s)
  T    (addTimed✓+ a P)    = ⊤'  ⊎'  T P 
  PT   (addTimed✓+ a P) (inj₁ _) = a
  PT   (addTimed✓+ a P) (inj₂ c) = PT P c
  Str+ (addTimed✓+  a P)  = addTimed✓Str a  (Str+ P)


