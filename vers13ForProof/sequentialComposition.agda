module sequentialComposition where

open import Size
open import Data.Sum
open import choiceSetU
open import process
open Process∞
open Process'
open Process

mutual 
   _⟫='_ : {i : Size} → {c₀ c₁ : Choice} → Process' i c₀
          → (ChoiceSet c₀ → Process' i c₁)
                      → Process' i c₁
   E    (P ⟫=' Q)          =  E    P
   Lab  (P ⟫=' Q)          =  Lab  P
   PE   (P ⟫=' Q) c        =  PE   P  c  ⟫='   Q
   I    (P ⟫=' Q)          =  I P ⊎' T P
   PI   (P ⟫=' Q) (inj₁ c) =  PI   P  c  ⟫='   Q
   PI   (P ⟫=' Q) (inj₂ c) =  Q (PT P c)
   T    (P ⟫=' Q)          =  ∅'
   PT   (P ⟫=' Q) ()




mutual 
   _⟫=_ : {i : Size} → {c₀ c₁ : Choice} → Process i c₀
          → (ChoiceSet c₀ → Process∞ i c₁)
                      → Process i c₁
   E    (P ⟫= Q)          = E   P
   Lab  (P ⟫= Q)          = Lab  P
   PE   (P ⟫= Q) c        = PE   P  c  ⟫=∞    Q
   I    (P ⟫= Q)          = I P ⊎' T P
   PI   (P ⟫= Q) (inj₁ c) = PI  P  c  ⟫=∞    Q
   PI   (P ⟫= Q) (inj₂ c) = Q (PT P c)
   T    (P ⟫= Q)          = ∅'
   PT   (P ⟫= Q) ()


   _⟫=∞_ : {i : Size} → {c₀ c₁ : Choice} → Process∞ i c₀
          → (ChoiceSet c₀ → Process∞ i c₁)
                      → Process∞ i c₁
   forcep (P ⟫=∞ Q)    =   forcep  P  ⟫= Q



