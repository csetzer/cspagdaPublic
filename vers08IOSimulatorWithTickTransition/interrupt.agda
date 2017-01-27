module interrupt where

open import Size
open import process
open import choiceSetU
open import choiceAuxFunction
open import dataAuxFunction
open import auxData
open import label
open import Data.String renaming (_++_ to _++s_)
open import showFunction
open import renamingResult 
open import Data.Sum
open Process∞
open Process+


△Res : Set → Set → Set
△Res A B = (A ⊎ B) ⊎ (A × B)

mutual
  _△∞∞_ : {c₀ c₁  : Choice} → {i : Size} → Process∞ i (ChoiceSet c₀) → Process∞ i (ChoiceSet c₁) → Process∞ i ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ (ChoiceSet c₀ × ChoiceSet c₁))
  forcep (P △∞∞  P') i = forcep P i △ forcep P' i 

  _△∞+_ : {c₀ c₁  : Choice} → {i : Size} → Process∞ i (ChoiceSet c₀) → Process+ i (ChoiceSet c₁) → Process∞ i ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ (ChoiceSet c₀ × ChoiceSet c₁))
  forcep (P △∞+  P') i = forcep P i △p+ P'

  _△+∞_ : {c₀ c₁  : Choice} → {i : Size} → Process+ i (ChoiceSet c₀) → Process∞ i (ChoiceSet c₁) → Process∞ i  ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ (ChoiceSet c₀ × ChoiceSet c₁))
  forcep (P △+∞  P') i = P △+p forcep P' i

  _△_ : {c₀ c₁  : Choice} → {i : Size} → Process i (ChoiceSet c₀) → Process i (ChoiceSet c₁) → Process i ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ (ChoiceSet c₀ × ChoiceSet c₁))
  node P      △ P'      = P △+p P'
  P           △ node P' = P △p+ P'
  terminate a △ terminate b = terminate (inj₂ (a ,, b))
   -- according to the rules when P terminaes it terminates and when Q terminates it can terminate
   -- 

  _△+p_ : {c₀ c₁  : Choice} → {i : Size} → Process+ i (ChoiceSet c₀) → Process i (ChoiceSet c₁) → Process i ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ (ChoiceSet c₀ × ChoiceSet c₁))
  P △+p  terminate b  = terminate (inj₁ (inj₂ b)) 
  -- an alternative would have been
  -- P △+p  terminate b  =  node (fmap+i ((λ a → inj₂ (a ,, b))) P) 
  -- that the tick for terminate b is not executed
  P △+p  node P'      = node (P △+ P')

  _△p+_ : {c₀ c₁  : Choice} → {i : Size} → Process i (ChoiceSet c₀) → Process+ i (ChoiceSet c₁) → Process i ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ (ChoiceSet c₀ × ChoiceSet c₁))
  terminate a △p+  P' = terminate (inj₁ (inj₁ a))
 -- node (fmap+i ((λ b → inj₂ (a ,, b))) P')  ("λ b → inj₂ (" ++s choice2String c a  ++s ",, b)"
  node P △p+ P'       = node (P △+ P')


  _△+_ : {c₀ c₁  : Choice} → {i : Size} → Process+ i (ChoiceSet c₀) → Process+ i (ChoiceSet c₁) → Process+ i  ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ (ChoiceSet c₀ × ChoiceSet c₁))
  E   (P △+ Q)                      = E P +'' E Q
  Lab (P △+ Q) (inj₁ x)             = Lab P x
  Lab (P △+ Q) (inj₂ x)             = Lab Q x
  PE  (P △+ Q) (inj₁ x)             = PE P x △∞+ Q 
  PE  (_△+_ {A}{B}{i} P Q) (inj₂ x) = fmap∞ (inj₁ ∘ inj₂) i (PE Q x)
  I   (P △+ Q)                      = I P +'' I Q
  PI  (P △+ Q) (inj₁ c)             = PI P c △∞+ Q 
  PI  (P △+ Q) (inj₂ c)             = P      △+∞ PI Q c 
  T   (P △+ Q)                      = T P +'' T Q
  PT (P △+ Q) (inj₁ c) = inj₁ (inj₁ (PT P c))
  PT (P △+ Q) (inj₂ c) = inj₁ (inj₂ (PT Q c)) 
  Str (P △+ Q)                      = (Str P ++s " \t △ \t " ++s Str Q)


{-

△Res : Set → Set → Set
△Res A B = (A ⊎ B) ⊎ (A × B)

mutual
  _△∞∞_ : {A B  : Set} → {i : Size} → Process∞ i A → Process∞ i B → Process∞ i (△Res A B)
  forcep (P △∞∞  P') i = forcep P i △ forcep P' i 

  _△∞+_ : {A B : Set} → {i : Size} → Process∞ i A → Process+ i B → Process∞ i (△Res A B)
  forcep (P △∞+  P') i = forcep P i △p+ P'

  _△+∞_ : {A : Set} → {B : Set} → {i : Size} → Process+ i A → Process∞ i B → Process∞ i (△Res A B)
  forcep (P △+∞  P') i = P △+p forcep P' i

  _△_ : {A B : Set} → {i : Size} → Process i A → Process i B → Process i (△Res A B)
  node P      △ P'      = P △+p P'
  P           △ node P' = P △p+ P'
  terminate a △ terminate b = terminate (inj₂ (a ,, b))
   -- according to the rules when P terminaes it terminates and when Q terminates it can terminate
   -- 

  _△+p_ : {A B : Set} → {i : Size} → Process+ i A → Process i B → Process i (△Res A B)
  P △+p  terminate b  = terminate (inj₁ (inj₂ b)) 
  -- an alternative would have been
  -- P △+p  terminate b  =  node (fmap+i ((λ a → inj₂ (a ,, b))) P) 
  -- that the tick for terminate b is not executed
  P △+p  node P'      = node (P △+ P')

  _△p+_ : {A B : Set} → {i : Size} → Process i A → Process+ i B → Process i (△Res A B)
  terminate a △p+  P' = terminate (inj₁ (inj₁ a)) -- node (fmap+i ((λ b → inj₂ (a ,, b))) P')  ("λ b → inj₂ (" ++s choice2String c a  ++s ",, b)"
  node P △p+ P'       = node (P △+ P')


  _△+_ : {A B : Set} → {i : Size} → Process+ i A → Process+ i B → Process+ i (△Res A B)
  E   (P △+ Q)                      = E P +'' E Q
  Lab (P △+ Q) (inj₁ x)             = Lab P x
  Lab (P △+ Q) (inj₂ x)             = Lab Q x
  PE  (P △+ Q) (inj₁ x)             = PE P x △∞+ Q 
  PE  (_△+_ {A}{B}{i} P Q) (inj₂ x) = fmap∞ (inj₁ ∘ inj₂) i (PE Q x)
  I   (P △+ Q)                      = I P +'' I Q
  PI  (P △+ Q) (inj₁ c)             = PI P c △∞+ Q 
  PI  (P △+ Q) (inj₂ c)             = P      △+∞ PI Q c 
  T   (P △+ Q)                      = T P +'' T Q
  PT (P △+ Q) (inj₁ c) = inj₁ (inj₁ (PT P c))
  PT (P △+ Q) (inj₂ c) = inj₁ (inj₂ (PT Q c)) 
  Str (P △+ Q)                      = (Str P ++s " \t △ \t " ++s Str Q)


-}
