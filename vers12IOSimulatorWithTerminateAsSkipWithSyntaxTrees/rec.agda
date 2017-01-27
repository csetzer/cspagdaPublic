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
open import CSPAgdaSyntax


mutual
  rec : {i : Size} → {c₀ c₁ : Choice}
         →  (name : Syntax c₁)
         →  (ChoiceSet  c₀ → Process+ (↑ i) (c₀ ⊎' c₁))
         →  ChoiceSet   c₀ 
         →  Process∞  i c₁ 
  forcep (rec name f a)  =   renameP name 
                             (f a ⟫=+p recaux name f)
  Syn∞   (rec name f a)  =   name

  recaux  : {i : Size} →  {c₀ c₁ : Choice}
         → (name : Syntax c₁)
         → (ChoiceSet c₀ → Process+ (↑ i) (c₀ ⊎' c₁))
         → (ChoiceSet c₀ ⊎ ChoiceSet c₁)
         → Process∞ i c₁
  recaux name f (inj₁ x)  =  rec    name f x 
  recaux name f (inj₂ x)  =  delay  (terminate x )



recAutoStr : {i : Size} → {c₀ c₁ : Choice}
       → (ChoiceSet c₀ → Process+ (↑ i) (c₀ ⊎' c₁))
       → ChoiceSet c₀ 
       → Process∞ i c₁ 
recAutoStr f a = rec (rec' (Syn+ ∘ f) a) f a 
