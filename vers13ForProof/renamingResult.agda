module renamingResult where

open import process
open Process∞
open Process∞
open Process
open Process'
open import Size
open import choiceSetU
open import sequentialComposition
open import dataAuxFunction



fmap' : {c₀ c₁ : Choice} 
          → (f : ChoiceSet c₀  → ChoiceSet c₁) 
          → {i : Size}
          → Process' i c₀ → Process' i c₁ 
E    (fmap' f P)   = E P
Lab  (fmap' f P) c = Lab P c
PE   (fmap' f P) c = fmap' f (PE P c)
I    (fmap' f P)   = I P
PI   (fmap' f P) c = fmap' f (PI P c)
T    (fmap' f P)   = T P
PT   (fmap' f P) c = f (PT P c)


mutual
  fmap : {c₀ c₁ : Choice} 
          → (f : ChoiceSet c₀  → ChoiceSet c₁) 
          → {i : Size}
          → Process i c₀ → Process i c₁ 
  E    (fmap f P)   = E P
  Lab  (fmap f P) c = Lab P c
  PE   (fmap f P) c = fmap∞ f (PE P c)
  I    (fmap f P)   = I P
  PI   (fmap f P) c = fmap∞ f (PI P c)
  T    (fmap f P)   = T P
  PT   (fmap f P) c = f (PT P c)

  fmap∞  : {c₀ c₁ : Choice} 
          → (f : ChoiceSet c₀  → ChoiceSet c₁) 
          → {i : Size}
          → Process∞ i c₀ → Process∞ i c₁ 
  forcep (fmap∞ f P) = fmap f (forcep P)

