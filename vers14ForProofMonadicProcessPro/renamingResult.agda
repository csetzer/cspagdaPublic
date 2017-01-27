module renamingResult where

open import process
open import Size
open import choiceSetU
open import sequentialComposition
open import dataAuxFunction
open import Data.String renaming (_++_ to _++s_)
open import showFunction

{-
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

-}

fmapStr : {c₀ c₁ : Choice} → (f : ChoiceSet c₀
          → ChoiceSet c₁) → String → String
fmapStr f str = "fmap("
                ++s  choiceFunctionToStringi f
                ++s "," ++s str ++s ")"


mutual
  fmap∞  : {c₀ c₁ : Choice} 
          → (f : ChoiceSet c₀  → ChoiceSet c₁) 
          → {i : Size}
          → Process∞ i c₀ → Process∞ i c₁ 
  forcep (fmap∞ f P)   = fmap f (forcep P)
  Str∞   (fmap∞  f P)  = fmapStr f (Str∞  P)


  fmap  : {c₀ c₁ : Choice} → (f : ChoiceSet c₀
          → ChoiceSet c₁) → {i : Size}
          → Process i c₀ → Process i c₁  
  fmap f (terminate a) = terminate (f a)
  fmap f (node P)      = node (fmap+ f P)


  fmap+ : {c₀ c₁ : Choice} 
          → (f : ChoiceSet c₀  → ChoiceSet c₁) 
          → {i : Size}
          → Process+ i c₀ → Process+ i c₁ 
  E    (fmap+ f P)   = E P
  Lab  (fmap+ f P) c = Lab P c
  PE   (fmap+ f P) c = fmap∞ f (PE P c)
  I    (fmap+ f P)   = I P
  PI   (fmap+ f P) c = fmap∞ f (PI P c)
  T    (fmap+ f P)   = T P
  PT   (fmap+ f P) c = f (PT P c)
  Str+ (fmap+ f P)   = fmapStr f (Str+ P)


