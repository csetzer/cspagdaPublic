module proofInterruptLaw where

open import process 
open import Size
open import choiceSetU
open import auxData
open import Data.Maybe
open import Data.Product
open import Data.Fin
open import Data.List
open import Data.Sum
open import label
open import dataAuxFunction
open import renamingResult
open import TraceWithoutSize
open import RefWithoutSize
open import primitiveProcess
open import interrupt
open import addTick
open import lemFmap
open import traceEquivalence



mutual
  stopInterruptᵣ : {c₀ c₁ : Choice} (P : Process ∞ c₁)
           → fmap inj₂ P ⊑  (STOP c₀ △ P)
  stopInterruptᵣ (terminate x) .[] .nothing (tnode empty) = empty (inj₂ x)
  stopInterruptᵣ (terminate x) .(efq _ ∷ l) m (tnode (extc l .m () x₂))
  stopInterruptᵣ (terminate x) l m (tnode (intc .l .m () x₂))
  stopInterruptᵣ (terminate x) .[] .(just (inj₂ x)) (tnode (terc (inj₁ Fin.zero))) = ter (inj₂ x)
  stopInterruptᵣ (terminate x) .[] .(just (inj₂ x)) (tnode (terc (inj₁ (Fin.suc ()))))
  stopInterruptᵣ (terminate x) .[] .(just (inj₁ (efq _))) (tnode (terc (inj₂ ())))
  stopInterruptᵣ (node x) .[] .nothing (tnode empty) = tnode empty
  stopInterruptᵣ (node x) .(efq _ ∷ l) m (tnode (extc l .m (inj₁ ()) x₂))
  stopInterruptᵣ (node x) .(Lab x y ∷ l) m (tnode (extc l .m (inj₂ y) x₂)) = tnode (extc l m y x₂ )
  stopInterruptᵣ (node x) l m (tnode (intc .l .m (inj₁ ()) x₂))
  stopInterruptᵣ (node x) l m (tnode (intc .l .m (inj₂ y) x₂)) = tnode (intc l m y (stopInt∞ᵣ l m (PI x y) x₂))
  stopInterruptᵣ (node x) .[] .(just (inj₁ (efq _))) (tnode (terc (inj₁ ())))
  stopInterruptᵣ (node x) .[] .(just (inj₂ (PT x y))) (tnode (terc (inj₂ y))) = tnode(terc y)

  stopInt∞ᵣ : {c₁ c₀ : Choice} (l   : List Label) (m : Maybe (ChoiceSet c₀ ⊎ ChoiceSet c₁)) (P : Process∞ ∞ c₁)
           →  (x₂ : Tr∞ l m (STOP+ c₀ △+∞ P )) →  Tr∞ l m (fmap∞ inj₂ P )
  forcet (stopInt∞ᵣ l m P x₂) = stopIntᵣ l m (forcep P) (forcet x₂)


  stopIntᵣ : {c₁ c₀ : Choice} (l   : List Label) (m : Maybe (ChoiceSet c₀ ⊎ ChoiceSet c₁)) (P : Process ∞ c₁)
           →  (x₂ : Tr l m (STOP+ c₀ △+p P )) →  Tr l m (fmap inj₂ P )
  stopIntᵣ l m P x₂ = stopInterruptᵣ P l m x₂


mutual
  stopInterrupt : {c₀ c₁ : Choice} (P : Process ∞ c₁)
           →  (STOP c₀ △ P)  ⊑   fmap inj₂ P
  stopInterrupt (terminate x) .[] .(just (inj₂ x)) (ter .(inj₂ x))      = tnode (terc (inj₁ zero))
  stopInterrupt (terminate x) .[] .nothing (empty .(inj₂ x))            = tnode empty
  stopInterrupt (node x) .[] .nothing (tnode empty)                     = tnode empty
  stopInterrupt (node x) .(Lab x x₁ ∷ l) m (tnode (extc l .m x₁ x₂))    = tnode (extc l m (inj₂ x₁) x₂)
  stopInterrupt (node x) l m (tnode (intc .l .m x₁ x₂))                 = tnode (intc l m (inj₂ x₁) (stopInt' l m (PI x x₁) x₂))
  stopInterrupt (node x) .[] .(just (inj₂ (PT x x₁))) (tnode (terc x₁)) = tnode (terc (inj₂ x₁))

  stopInt∞ : {c₁ c₀ : Choice} (l : List Label)
             (m : Maybe (ChoiceSet c₀ ⊎ ChoiceSet c₁))
             (P : Process∞ ∞ c₁)
             → (x₂ :  Tr∞ l m (fmap∞ inj₂ P ))
             → Tr∞ l m (STOP+ c₀ △+∞ P )
  forcet (stopInt∞ l m P x₂) = stopInt l m (forcep P) (forcet x₂)


  stopInt : {c₁ c₀ : Choice} (l : List Label)
            (m : Maybe (ChoiceSet c₀ ⊎ ChoiceSet c₁))
            (P : Process ∞ c₁)
            → (x₁ : Tr l m (fmap inj₂ P ))
            →  Tr l m (STOP+ c₀ △+p P )
  stopInt l m P x₂ = stopInterrupt P l m x₂


  stopInt' : {c₁ c₀ : Choice} (l : List Label)
             (m : Maybe (ChoiceSet c₀ ⊎ ChoiceSet c₁))
             (P : Process∞ ∞ c₁)
           → (x₁ : Tr∞ l m (fmap∞ inj₂ P ))
           →  Tr∞ l m (STOP+ c₀ △+∞ P)
  forcet (stopInt' l m P x₂) =  stopInterrupt (forcep P) l m (forcet x₂)


≡stopInterrupt : {i : Size} {c₀  : Choice}
                → (P : Process ∞ c₀)
                → ( fmap inj₂ P) ≡ (STOP c₀ △ P)
≡stopInterrupt P = (stopInterruptᵣ P) , (stopInterrupt P)




