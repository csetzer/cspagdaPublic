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
open import CSPAgdaSyntax

mutual
   _/∞_ : {i : Size} → {c : Choice}
          → (hide : Label → Bool)
          → Process∞ i c
          → Process∞ i c
   forcep (f /∞ P)   =   f / (forcep  P)
   Syn∞   (f /∞  P)   =  f /' (Syn∞    P)


   _/_ : {i : Size} → {c : Choice} 
           → (hide : Label → Bool)
           → Process i c
           → Process i c
   f / (node P)       =  node      (f /+ P)
   f / (terminate x)  =  terminate x


   _/+_ : {i : Size} → {c : Choice} 
           → (hide : Label → Bool) → Process+ i c 
           → Process+ i c
   E    (f /+ P)  = subset' (E P) (¬b ∘ (f ∘ (Lab P)))
   Lab  (f /+ P)  c = Lab  P (projSubset c)  
   PE   (f /+ P)  c = f /∞ (PE P (projSubset c))
   I    (f /+ P)  = I P ⊎' subset' (E P) (f ∘ Lab P)
   PI   (f /+ P)  (inj₁ c) = PI P c
   PI   (f /+ P)  (inj₂ c) = PE P (projSubset c)
   T    (f /+ P)  = T   P
   PT   (f /+ P)  = PT  P
   Syn+ (f /+ P)  = f /' (Syn+ P)





mutual
   Hide∞ : {i : Size} → {c : Choice}
          → (hide : Label → Bool)
          → Process∞ i c
          → Process∞ i c
   forcep (Hide∞ f  P)   =  Hide    f  (forcep  P)
   Syn∞   (Hide∞ f  P)   =  Hide' f  (Syn∞    P)


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
   PI   (Hide+ f P)  (inj₁ c) = Hide∞ f (PI P c)
   PI   (Hide+ f P)  (inj₂ c) = Hide∞ f (PE P (projSubset c))
   T    (Hide+ f P)  = T   P
   PT   (Hide+ f P)  = PT  P
   Syn+ (Hide+ f P)  = Hide' f (Syn+ P)
