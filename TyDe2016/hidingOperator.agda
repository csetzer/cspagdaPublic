module hidingOperator where 

open import Size 
open import process 
open Process∞
open Process+
open import label
open import Data.Bool renaming (T to Tb)
open import Data.String.Base
open import auxData
open import dataAuxFunction
open import choiceSetU
open import Data.Sum
open import showLabelP
open import addTickOperator

HideStr : (f : Label → Bool) → String → String
HideStr f str = "Hide  " ++ labelBoolFunToString f ++ " " ++ str



mutual
   Hide∞ : {i : Size} → {c : Choice}
          → (hide : Label → Bool)
          → Process∞ i c
          → Process∞ i c
   forcep (Hide∞ f  P)   =  Hide    f  (forcep  P)
   Str∞   (Hide∞ f  P)   =  HideStr f  (Str∞    P)


   Hide : {i : Size} → {c : Choice} 
           → (hide : Label → Bool)
           → Process i c
           → Process i c
   Hide  f  (node P)       =  node      (Hide+ f P)
   Hide  f  (terminate x)  =  terminate x


   Hide+ : {i : Size} → {c : Choice} 
           → (hide : Label → Bool) → Process+ i c 
           → Process+ i c
   E    (Hide+ f P)  = subset' (E P) (¬b ∘ (f ∘ (Lab P)))
   Lab  (Hide+ f P)  c = Lab  P (projSubset c)  
   PE   (Hide+ f P)  c = Hide∞ f (PE P (projSubset c))
   I    (Hide+ f P)  = I P ⊎' subset' (E P) (f ∘ Lab P)
   PI   (Hide+ f P)  (inj₁ c) = Hide∞ f  (PI P c)
   PI   (Hide+ f P)  (inj₂ c) = Hide∞ f  (PE P (projSubset c))
   T    (Hide+ f P)  = T   P
   PT   (Hide+ f P)  = PT  P
   Str+ (Hide+ f P)  = HideStr f (Str+ P)
