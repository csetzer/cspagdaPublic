{-# OPTIONS --copatterns #-}

module rec where
open import Size
open import choiceSetU 
open import process
open import dataAuxFunction
open import auxData
open import Data.String
open Process∞
open Process+
open import sequentialComposition
open import Data.Sum


{-
node E Lab PE I PI Stat ⟫=+'' q = node E Lab ((λ x → PE x ⟫=∞ q))
                                     I (((λ x → PI x ⟫=∞ q))) Stat
-}




mutual
  rec : (i : Size) → {c₀ c₁ : Choice}
         → (ChoiceSet c₀ → Process+ (↑ i) ((ChoiceSet c₀ ⊎ ChoiceSet c₁)))
         → (ChoiceSet c₀) → Process∞ i (ChoiceSet c₁ )
  forcep (rec i f x) j = f x ⟫=+p recaux j f  

  recaux  : (i : Size) →  {c₀ c₁ : Choice}
           → (ChoiceSet c₀ → Process+ (↑ i) ((ChoiceSet c₀ ⊎  ChoiceSet c₁)))
           → ((ChoiceSet c₀ ⊎ ChoiceSet c₁)) → Process∞ i (ChoiceSet c₁)
  recaux i f (inj₁ x) = rec i f x 
  recaux i f (inj₂ x) =  delay i (terminate x )

