module sequentialComposition where

open import Size
open import Data.Sum
open import choiceSetU
open import process
open import Data.String    renaming (_++_ to _++s_)
open import showFunction
open import dataAuxFunction


_⟫=Str_ : {c₀ : Choice} → String 
         → (ChoiceSet c₀ → String)  → String
s ⟫=Str f = s  ++s ";" ++s choice2Str2Str f


mutual 
   _⟫=∞_ : {i : Size} → {c₀ c₁ : Choice} 
          →  Process∞ i c₀
          →  (ChoiceSet c₀ → Process∞ i c₁)
          →  Process∞ i c₁
   forcep (P ⟫=∞ Q)    =   forcep P  ⟫= Q
   Str∞   (P ⟫=∞ Q)    =   Str∞ P ⟫=Str (Str∞ ∘ Q)

   _⟫=_ : {i : Size} → {c₀ c₁ : Choice} 
          →  Process i c₀
          →  (ChoiceSet c₀ → Process∞ (↑ i) c₁)
          →  Process i c₁
   node      P  ⟫=  Q  =  node    (P ⟫=+ Q)
   terminate x  ⟫=  Q  =  forcep  (Q x) 

   _⟫=+_ : {i : Size} → {c₀ c₁ : Choice} 
          →  Process+ i c₀
          →  (ChoiceSet c₀ → Process∞ i c₁)
          →  Process+ i c₁
   E    (P ⟫=+ Q)           =  E    P
   Lab  (P ⟫=+ Q)           =  Lab  P
   PE   (P ⟫=+ Q) c         =  PE  P  c  ⟫=∞    Q
   I    (P ⟫=+ Q)           =  I P ⊎' T P
   PI   (P ⟫=+ Q) (inj₁ c)  =  PI  P  c  ⟫=∞    Q
   PI   (P ⟫=+ Q) (inj₂ c)  =  Q (PT P c)
   T    (P ⟫=+ Q)           =  ∅'
   PT   (P ⟫=+ Q) ()
   Str+ (P ⟫=+ Q)  =  Str+ P ⟫=Str (Str∞ ∘ Q)


_⟫=+p_ : {i : Size} → {c₀ c₁ : Choice} → Process+ i c₀
            → ( ChoiceSet c₀ → Process∞ i c₁)
                       → Process i c₁
P ⟫=+p Q = node (P ⟫=+ Q)



