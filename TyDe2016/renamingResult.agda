module renamingResult where

open import Data.String renaming (_++_ to _++s_)
open import process
open Process∞
open Process+
open import Size
open import choiceSetU
open import showFunction
open import sequentialComposition
open import dataAuxFunction

fmap : {c₀ c₁ : Choice} → {i : Size}
       → (f : ChoiceSet c₀ → ChoiceSet c₁)
       → Process i c₀ → Process i c₁  
fmap f P = P ⟫=  (delay ∘ (terminate ∘ f))

fmap+ : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size}            → Process+ i c₀ 
         → Process+ i c₁ 
fmap+ f P = P ⟫=+  (delay ∘ (terminate ∘ f))

fmap∞ : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size}
         → Process∞ i c₀ 
         → Process∞ i c₁  
fmap∞ f P = P ⟫=∞ (delay ∘ (terminate ∘ f))

mutual
  fmapStr : {c₀ c₁ : Choice} → (f : ChoiceSet c₀
            → ChoiceSet c₁) → String → String
  fmapStr f str = "fmap("
                        ++s  choiceFunctionToStringi f
                        ++s "," ++s str ++s ")"

  fmap∞' : {c₀ c₁ : Choice} → (f : ChoiceSet c₀
          → ChoiceSet c₁) → {i : Size}
          → Process∞ i c₀ → Process∞ i c₁  
  forcep (fmap∞'  f P)   = fmap' f (forcep P )
  Str∞   (fmap∞'  f P)   = fmapStr f (Str∞  P)


  fmap'  : {c₀ c₁ : Choice} → (f : ChoiceSet c₀
          → ChoiceSet c₁) → {i : Size}
          → Process i c₀ → Process i c₁  
  fmap' f (terminate a) = terminate (f a)
  fmap' f (node P)      = node (fmap+' f P)

  fmap+' : {c₀ c₁ : Choice} → (f : ChoiceSet c₀
          → ChoiceSet c₁) → {i : Size}
          → Process+ i c₀ → Process+ i c₁ 
  E    (fmap+' f P)   = E P
  Lab  (fmap+' f P) c = Lab P c
  PE   (fmap+' f P) c = fmap∞' f (PE P c)
  I    (fmap+' f P)   = I P
  PI   (fmap+' f P) c = fmap∞' f (PI P c)
  T    (fmap+' f P)   = T P
  PT   (fmap+' f P) c = f (PT P c)
  Str+ (fmap+' f P)   = fmapStr f (Str+ P)


  fmapi : {c₀ c₁ : Choice} → (f : ChoiceSet c₀
         → ChoiceSet c₁)  → (i : Size)
         → Process i c₀ → Process i c₁  
  fmapi f i P = fmap' f {i} P

  fmap+i : {c₀ c₁ : Choice} → (f : ChoiceSet c₀
           → ChoiceSet c₁) → (i : Size)
           → Process+ i c₀ → Process+ i c₁ 
  fmap+i f i P = fmap+' f {i} P

  fmap∞i : {c₀ c₁ : Choice} → (f : ChoiceSet c₀
           → ChoiceSet c₁) → (i : Size)
           → Process∞ i c₀ → Process∞ i c₁  
  fmap∞i f i  =  fmap∞' f {i} 
