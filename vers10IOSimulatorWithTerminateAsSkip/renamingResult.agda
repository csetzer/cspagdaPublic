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

fmapStr : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) 
          → String → String
fmapStr f str = "(fmap " ++s  choiceFunToStr↓ f ++s " " ++s  str ++s ")"



mutual
  fmap∞ : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size} 
          → Process∞ i c₀ → Process∞ i c₁  
  forcep (fmap∞  f P) = fmap f (forcep P)
  Str∞   (fmap∞  f P) = fmapStr f (Str∞  P)

  fmap  : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size} 
          → Process i c₀  
          → Process i c₁  
  fmap f (terminate a) = terminate (f a)
  fmap f (node P)      = node (fmap+ f P)

  fmap+ : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size} 
          → Process+ i c₀ 
          → Process+ i c₁ 
  E    (fmap+  f P)   = E P
  Lab  (fmap+  f P) c = Lab P c
  PE   (fmap+  f P) c = fmap∞ f (PE P c)
  I    (fmap+  f P)   = I P
  PI   (fmap+  f P) c = fmap∞ f (PI P c)
  T    (fmap+  f P)   = T P
  PT   (fmap+  f P) c = f (PT P c)
  Str+ (fmap+  f P)   = fmapStr f (Str+ P)


  fmapi : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → (i : Size)
          → Process i c₀ 
          → Process i c₁  
  fmapi f i P = fmap f {i} P

  fmap+i : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → (i : Size)           → Process+ i c₀ 
           → Process+ i c₁ 
  fmap+i f i P = fmap+ f {i} P

  fmap∞i : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → (i : Size)
           → Process∞ i c₀ 
           → Process∞ i c₁  
  fmap∞i f i  =  fmap∞ f {i} 




fmap' : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size} 
        → Process i c₀ 
        → Process i c₁  
fmap' f P = P ⟫=  (delay ∘ (terminate ∘ f))

fmap+' : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size}         → Process+ i c₀ 
         → Process+ i c₁ 
fmap+' f P = P ⟫=+  (delay ∘ (terminate ∘ f))

fmap∞' : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size}
         → Process∞ i c₀ 
         → Process∞ i c₁  
fmap∞' f P = P ⟫=∞ (delay ∘ (terminate ∘ f))


mutual

  fmapCustomStr : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) 
            → (fname : String)
            → String → String
  fmapCustomStr f fname str = "(fmap " ++s  fname ++s " " ++s str ++s ")"


  fmapCustom∞ : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size} 
          → (fname : String)
          → Process∞ i c₀ → Process∞ i c₁  
  forcep (fmapCustom∞  f fname P) = fmapCustom f fname (forcep P)
  Str∞   (fmapCustom∞  f fname P) = fmapCustomStr f fname (Str∞  P)

  fmapCustom  : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size} 
          → (fname : String)
          → Process i c₀  
          → Process i c₁  
  fmapCustom f fname (terminate a) = terminate (f a)
  fmapCustom f fname (node P)      = node (fmapCustom+ f fname P)

  fmapCustom+ : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size} 
          → (fname : String)
          → Process+ i c₀ 
          → Process+ i c₁ 
  E    (fmapCustom+  f fname P)   = E P
  Lab  (fmapCustom+  f fname P) c = Lab P c
  PE   (fmapCustom+  f fname P) c = fmapCustom∞ f fname (PE P c)
  I    (fmapCustom+  f fname P)   = I P
  PI   (fmapCustom+  f fname P) c = fmapCustom∞ f fname (PI P c)
  T    (fmapCustom+  f fname P)   = T P
  PT   (fmapCustom+  f fname P) c = f (PT P c)
  Str+ (fmapCustom+  f fname P)   = fmapCustomStr f fname (Str+ P)
