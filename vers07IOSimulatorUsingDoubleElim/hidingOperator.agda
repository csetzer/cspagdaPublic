module hidingOperator where 

open import Size 
open import process 
open Process∞
open Process+
open import label
open import Data.Bool
open import Data.String.Base
open import auxData
open import dataAuxFunction
open import choiceSetU
open import Data.Sum
open import showLabelP



mutual 
   Hide∞ : (i : Size) → {c : Choice}
          → (hide : Label → Bool)
          → Process∞ i (ChoiceSet c)
          → Process∞ i (ChoiceSet c)
   forcep (Hide∞ i f  P) j = Hide j f (forcep P j)

   Hide : (i : Size) → {c : Choice} 
           → (hide : Label → Bool)
           → Process i (ChoiceSet c)
           → Process i (ChoiceSet c)
   Hide i {c} f (node P) = node (Hide+ i {c} f P)
   Hide i f (terminate x) = terminate x

   Hide+ : (i : Size) → {c : Choice} 
           → (hide : Label → Bool)
           → Process+ i (ChoiceSet c)
           → Process+ i (ChoiceSet c)
   E   (Hide+ i f P)        = subset' (E P) (¬b ∘ (f ∘ (Lab P)))
   Lab (Hide+ i f P) c      = Lab P (projSubset c)   -- 
   PE  (Hide+ i f P) c      = Hide∞ i f (PE P (projSubset c))
   I   (Hide+ i f P)        = I P +'' subset' (E P) (f ∘ Lab P)
   PI (Hide+ i f P) (inj₁ c) = Hide∞ i f (PI P c)
   PI (Hide+ i f P) (inj₂ c) = Hide∞ i f (PE P (projSubset c))
   Str (Hide+ i f P)        = "Hide  " ++ (labelBoolFunToString f) ++ " " ++ Str P

