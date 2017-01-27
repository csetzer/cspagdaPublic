module renamingResultOriginal where

open import Data.String renaming (_++_ to _++s_)
open import process
open Process∞
open Process+
open import Size
open import choiceSetU
open import showFunction
open import CSPAgdaSyntax

mutual

  fmapStr : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) 
            → String → String
  fmapStr f str = "fmap(" ++s  choiceFunctionToStringi f ++s "," ++s str ++s ")"


  fmap∞ : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → (i : Size) 
          → Process∞ i c₀ → Process∞ i c₁  
  forcep (fmap∞  f i P) {j} = fmap f j (forcep P {j})
  Syn∞   (fmap∞  f i P)     = fmaps f (Syn∞  P)

  fmap  : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → (i : Size) 
          → Process i c₀  
          → Process i c₁  
  fmap f i (terminate a) = terminate (f a)
  fmap f i (node P)      = node (fmap+ f i P)

  fmap+ : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → (i : Size) 
          → Process+ i c₀ 
          → Process+ i c₁ 
  E    (fmap+  f i P)   = E P
  Lab  (fmap+  f i P) c = Lab P c
  PE   (fmap+  f i P) c = fmap∞ f i (PE P c)
  I    (fmap+  f i P)   = I P
  PI   (fmap+  f i P) c = fmap∞ f i (PI P c)
  T    (fmap+  f i P)   = T P
  PT   (fmap+  f i P) c = f (PT P c)
  Syn+ (fmap+  f i P)   = fmaps f (Syn+ P)


  fmapi : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size} 
          → Process i c₀ 
          → Process i c₁  
  fmapi f {i} P = fmap f i P

  fmap+i : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size}           → Process+ i c₀ 
           → Process+ i c₁ 
  fmap+i f {i} P = fmap+ f i P

  fmap∞i : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → {i : Size}
           → Process∞ i c₀ 
           → Process∞ i c₁  
  fmap∞i f {i}  =  fmap∞ f i 
