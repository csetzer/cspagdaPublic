module extchoice where

open import Size
open import process
open Process∞
open Process
open import choiceSetU
open import dataAuxFunction
open import auxData
open import label
open import renamingResult
open import Data.Sum
open import addTick


mutual
   _□_ : {c₀ c₁ : Choice} → {i : Size} 
        → Process i c₀ → Process i c₁  
        → Process i (c₀ ⊎' c₁)
   E    (P □ Q)           = E P ⊎' E Q
   Lab  (P □ Q) (inj₁ x)  = Lab P x
   Lab  (P □ Q) (inj₂ x)  = Lab Q x
   PE   (P □ Q) (inj₁ x)  = fmap∞ inj₁ (PE P x)
   PE   (P □ Q) (inj₂ x)  = fmap∞ inj₂ (PE Q x)
   I    (P □ Q)           = I P ⊎'  I Q
   PI   (P □ Q) (inj₁ c)  = PI P c □∞p Q 
   PI   (P □ Q) (inj₂ c)  = P      □p∞ PI Q c
   T    (P □ Q)           = T P ⊎' T Q
   PT   (P □ Q) (inj₁ c)  = inj₁ (PT P c)
   PT   (P □ Q) (inj₂ c)  = inj₂ (PT Q c)

   _□∞∞_ : {c₀ c₁  : Choice} → {i : Size} 
          → Process∞ i c₀ → Process∞ i c₁
          → Process∞ i (c₀ ⊎' c₁)
   forcep (P □∞∞  Q)  = forcep P  □  forcep Q  


   _□∞p_ : {c₀ c₁  : Choice} → {i : Size} 
          → Process∞ i c₀ → Process i c₁
          → Process∞ i  (c₀ ⊎' c₁)
   forcep (P  □∞p  Q)   =  forcep  P  □   Q
  

   _□p∞_ : {c₀ c₁  : Choice} → {i : Size} 
          → Process i c₀ → Process∞ i c₁
          → Process∞ i  (c₀ ⊎' c₁)
   forcep  (P  □p∞   Q)  =  P      □   forcep Q 
 
