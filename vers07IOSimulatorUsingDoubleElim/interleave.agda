module interleave where 

open import Size
open import process
open Process∞
open Process+
open import choiceSetU
open import choiceAuxFunction
open import dataAuxFunction
open import auxData
open import label
open import Data.String renaming (_++_ to _++s_)
open import showFunction
open import Data.Sum
open import renamingResult

mutual
   _|||∞_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process∞ i (ChoiceSet c₀)
          → Process∞ i (ChoiceSet c₁)
          → Process∞ i ((ChoiceSet c₀) × (ChoiceSet c₁))
   forcep (P |||∞  Q) j = forcep P j  ||| forcep Q j     

   _|||_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process i (ChoiceSet c₀)
          → Process i (ChoiceSet c₁)
          → Process i ((ChoiceSet c₀) × (ChoiceSet c₁))
   node P      |||  node Q     = node (P |||++ Q)
   terminate a |||  Q          = fmapi (λ b → (a ,, b)) Q
   P           ||| terminate b = fmapi (λ a → (a ,, b)) P

   _|||∞+_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process∞ i (ChoiceSet c₀)
          → Process+ i (ChoiceSet c₁)
          → Process∞ i ((ChoiceSet c₀) × (ChoiceSet c₁))
   forcep (P |||∞+ Q) j  = node ((forcep P j) |||p+ Q)

   _|||+∞_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process+ i (ChoiceSet c₀)
          → Process∞ i (ChoiceSet c₁)
          → Process∞ i ((ChoiceSet c₀) × (ChoiceSet c₁))
   forcep (P |||+∞ Q) j  = node (P |||+p  (forcep Q j))

   _|||p+_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process  i (ChoiceSet c₀)
          → Process+ i (ChoiceSet c₁)
          → Process+  i ((ChoiceSet c₀) × (ChoiceSet c₁))
   terminate a |||p+ Q = fmap+i (λ b → (a ,, b)) Q
   node P      |||p+ Q = P |||++ Q


   _|||+p_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process+  i (ChoiceSet c₀)
          → Process i (ChoiceSet c₁)
          → Process+  i ((ChoiceSet c₀) × (ChoiceSet c₁))
   P |||+p terminate b = fmap+i (λ a → (a ,, b)) P
   P |||+p node Q      = P |||++ Q



   _|||++_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process+ i (ChoiceSet c₀)
          → Process+ i (ChoiceSet c₁)
          → Process+ i ((ChoiceSet c₀) × (ChoiceSet c₁))
   E    (P |||++ Q ) =  E P +'' E Q
   Lab  (P |||++ Q ) (inj₁ c) = Lab P c
   Lab  (P |||++ Q ) (inj₂ c) = Lab Q c
   PE (P |||++ Q ) (inj₁ c) = PE P c |||∞+  Q
   PE (P |||++ Q ) (inj₂ c) = P      |||+∞  PE Q c
   I    (P |||++ Q ) =  I P +'' I Q
   PI   (P |||++ Q ) (inj₁ c) =   PI P c |||∞+   Q
   PI   (P |||++ Q ) (inj₂ c) =   P      |||+∞   PI Q c
   Str  (P |||++ Q )   =  Str P ++s "|||" ++s Str Q


infixl 10 _|||∞_  
infixl 10 _|||_  


