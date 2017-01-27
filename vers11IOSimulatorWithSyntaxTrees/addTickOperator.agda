module addTickOperator where

open import Size
open import process
open import choiceSetU
open import primitiveProcess
open import Data.Sum
open import Data.String renaming (_++_ to _++s_)
open Process∞
open Process+
open import syntaxOfCSPAgda

choiceFunctionAddEl : {ca : Choice} → (c : Choice) 
                      → (f : ChoiceSet c  → ChoiceSet ca)
                      → ChoiceSet ca 
                      → ChoiceSet (fin 1 ⊎' c)  
                      → ChoiceSet ca
choiceFunctionAddEl c f a (inj₁ x) = a
choiceFunctionAddEl c f a (inj₂ y) = f y

mutual
  addTickStr : {ca : Choice} → (c : Choice) 
               → (f : ChoiceSet c → ChoiceSet ca) → 
               String →  String 
  addTickStr c f s = "Something" ++s s

  addTick∞ : {ca : Choice} → {i : Size} → (c : Choice) 
             → (f : ChoiceSet c → ChoiceSet ca)
             → Process∞ i ca
             → Process∞ i ca
  forcep (addTick∞ c f  P) = addTick    c f (forcep P)
  Syn∞   (addTick∞ c f  P) = addTick' c f (Syn∞ P)

  addTick : {ca : Choice} → {i : Size} → (c : Choice) → (f : ChoiceSet c → ChoiceSet ca)
             → Process i ca
             → Process i ca
  addTick c f (terminate a) = MSKIP (fin 1 ⊎' c ) (choiceFunctionAddEl c f a) -- 
  addTick c f (node Q) = node (addTick+ c f Q)


  addTick+ : {ca : Choice} → {i : Size} → (c : Choice) → (f : ChoiceSet c → ChoiceSet ca)
             → Process+ i ca
             → Process+ i ca
  E    (addTick+ c f P)          = E P
  Lab  (addTick+ c f P) x        = Lab P x
  PE   (addTick+ c f P) x        = PE P x
  I    (addTick+ c f P)          = I P
  PI   (addTick+ c f P) x        = PI P x
  T    (addTick+ c f P)          = c ⊎' T P
  PT   (addTick+ c f P) (inj₁ x) = f x
  PT   (addTick+ c f P) (inj₂ y) = PT P y
  Syn+ (addTick+ c f P)          = addTick' c f (Syn+ P)
