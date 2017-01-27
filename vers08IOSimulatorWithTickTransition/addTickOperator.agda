module addTickOperator where

open import Size
open import process
open import choiceSetU
open import primitiveProcess
open import Data.Sum
open import Data.String renaming (_++_ to _++s_)
open Process∞
open Process+

choiceFunctionAddEl : {A : Set} → (c : Choice) → (f : ChoiceSet c  → A)
                      → A → ChoiceSet (fin 1 +'' c)  → A
choiceFunctionAddEl c f a (inj₁ x) = a
choiceFunctionAddEl c f a (inj₂ y) = f y

mutual
  addTick∞ : {A : Set} → {i : Size} → (c : Choice) → (f : ChoiceSet c → A)
             → Process∞ i A 
             → Process∞  i A
  forcep (addTick∞ {A} {i} c f  P) j = addTick {A} {j} c f  (forcep P j)

  addTick : {A : Set} → {i : Size} → (c : Choice) → (f : ChoiceSet c → A)
             → Process i A 
             → Process i A
  addTick {A} {i} c f (terminate a) = MSKIP i A (fin 1 +'' c ) (choiceFunctionAddEl c f a) -- 
  addTick c f (node Q) = node (addTick+ c f Q)


  addTick+ : {A : Set} → {i : Size} → (c : Choice) → (f : ChoiceSet c → A)
             → Process+ i A 
             → Process+ i A
  E   (addTick+ c f P)          = E P
  Lab (addTick+ c f P) x        = Lab P x
  PE  (addTick+ c f P) x        = PE P x
  I   (addTick+ c f P)          = I P
  PI  (addTick+ c f P) x        = PI P x
  T   (addTick+ c f P)          = c +'' T P
  PT  (addTick+ c f P) (inj₁ x) = f x
  PT  (addTick+ c f P) (inj₂ y) = PT P y
  Str (addTick+ c f P)          = "Something" ++s Str P
