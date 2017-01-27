{-# OPTIONS --show-implicit #-}

module MonadicLaw3 where 


open import Data.Fin
open import process
open import sequentialCompositionRev
open import TraceWithoutSize
open Tr∞
open import Size
open import choiceSetU
open import auxData
open import Data.Maybe
open import Data.Product
open import interleave
open import Data.List
open import Data.Sum
open import label
open import renamingResult
open import RefWithoutSize
open import dataAuxFunction





lemTrTerminateBind : (c : Choice)(P : Process+ ∞ c)(x : ChoiceSet (T P))
                     → Tr∞ [] (just (PT P x)) (PI (P ⟫=+ terminate) (inj₂ x))
forcet (lemTrTerminateBind c P x) = ter (PT P x)


lemTrTerminateBind' : (c₀ c₁ c₂ : Choice)
                      (P : Process+ ∞ c₀)
                      (Q : ChoiceSet c₀ → Process ∞ c₁)
                      (R : ChoiceSet c₁ → Process ∞ c₂)
                      (x  : Fin 0)
                     → Tr∞ [] (just (PT (_⟫=+_ P (λ x₁ → _⟫=_ (Q x₁) R)) x))(PI (_⟫=+_ (_⟫=+_ P Q) R) (inj₂ x))
forcet (lemTrTerminateBind'  c P Q R x q ())


mutual
  monadicLaw₁₋₃ : {c₀ c₁ c₂ : Choice} (P : Process ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → ((P  ⟫=  Q) ⟫= R)  ⊑  (P  ⟫=  ( λ x → Q x ⟫= R  ))
  monadicLaw₁₋₃  {c₀} {c₁} {c₂} (terminate x) Q R l m q = q
  monadicLaw₁₋₃  {c₀} {c₁} {c₂} (node x) Q R l m q = tnode (monadicLaw₁₋₃₊ x Q R l m (forcet' l m q))


  monadicLaw₁₋₃₊ : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → ((P  ⟫=+  Q) ⟫=+ R)  ⊑+  (P  ⟫=+  ( λ x → Q x ⟫= R  ))
  monadicLaw₁₋₃₊ P Q R .[] .nothing empty = empty
  monadicLaw₁₋₃₊ P Q R .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (monadicLaw₁₋₃∞ (PE P x) Q R l m x₁)
  monadicLaw₁₋₃₊ P Q R l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₁ (inj₁ x)) (monadicLaw₁₋₃∞ (PI P x) Q R l m x₁)
  monadicLaw₁₋₃₊ P Q R l m (intc .l .m (inj₂ y) x₁) =  intc l m (inj₁ (inj₂ y)) (monadPT+ P Q R y l m x₁)
  monadicLaw₁₋₃₊ {c₀}{c₁}{c₂} P Q R .[] .(just (PT (P ⟫=+ (λ x → Q x ⟫= R)) x)) (terc x) = intc [] (just (PT (_⟫=+_  P (λ x₁ → _⟫=_ (Q x₁) R)) x))  (inj₂ x) (lemTrTerminateBind' c₀ c₁ c₂ P Q R x)

  monadicLaw₁₋₃∞ : {c₀ c₁ c₂ : Choice} (P : Process∞ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → ((P  ⟫=∞  Q) ⟫=∞ R)  ⊑∞  (P  ⟫=∞  ( λ x → Q x ⟫= R ))
  forcet (monadicLaw₁₋₃∞ {c₀} {c₁} {c₂} P Q R l m q) =  monadicLaw₁₋₃ (forcep P) Q R l m (forcet q)



  monadPT+ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)(Q : ChoiceSet c₀ → Process ∞ c₁)
                  → (R  : ChoiceSet c₁ → Process ∞ c₂)
                  → (y  : ChoiceSet (T P))
                  → (l  : List Label)
                  → (m  : Maybe (ChoiceSet c₂))
                  → (x : Tr∞ l m (PI (P ⟫=+ (λ x → Q x ⟫= R)) (inj₂ y)))
                  →      Tr∞ l m (PI (P ⟫=+ Q) (inj₂ y) ⟫=∞ R)
  forcet (monadPT+  P Q R y l m tr) = forcet tr


