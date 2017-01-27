module rec where

open import Data.String renaming (_++_ to _++s_)
open import Data.Sum
open import Size
open import choiceSetU 
open import process
open Process∞
open Process+
open import dataAuxFunction
open import auxData
open import sequentialComposition
open import showFunction
open import renamingProcess

mutual
  rec : {i : Size} → {c₀ c₁ : Choice}
         →  (name : String)
         →  (ChoiceSet  c₀ → Process+ (↑ i) (c₀ ⊎' c₁))
         →  ChoiceSet   c₀ 
         →  Process∞    i c₁ 
  forcep (rec name f a)  =   renameP name 
                             (f a ⟫=+p recaux name f)
  Str∞   (rec name f a)  =   name

  recaux  : {i : Size} →  {c₀ c₁ : Choice}
         → (name : String)
         → (ChoiceSet c₀ → Process+ (↑ i) (c₀ ⊎' c₁))
         → (ChoiceSet c₀ ⊎ ChoiceSet c₁)
         → Process∞ i c₁
  recaux name f (inj₁ x)  =  rec    name f x 
  recaux name f (inj₂ x)  =  delay  (terminate x )



recStr : {c₀ : Choice} → (ChoiceSet c₀ → String) → ChoiceSet c₀ → String
recStr f a = "rec(" ++s choice2Str2Str f ++s "," ++s choice2Str a ++s ")"


recAutoStr : {i : Size} → {c₀ c₁ : Choice}
       → (ChoiceSet c₀ → Process+ (↑ i) (c₀ ⊎' c₁))
       → ChoiceSet c₀ 
       → Process∞ i c₁ 
recAutoStr f a = rec (recStr (Str+ ∘ f) a) f a 
