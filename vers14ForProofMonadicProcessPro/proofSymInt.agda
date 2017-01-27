module proofSymInt where

open import process 
open import indTr
open Tr∞
open import Size
open import choiceSetU
open import auxData
open import Data.Maybe
open import Data.Product
open import Data.Fin
open import interleave
open import Data.List
open import Data.Sum
open import label
open import renamingResult
open import refinement
open import dataAuxFunction
open import externalChoice
open import addTick
open import intChoiceNew


swap⊎ : {c₀ c₁ : Choice} → ChoiceSet (c₀ ⊎' c₁) → ChoiceSet (c₁ ⊎' c₀)
swap⊎ (inj₁ x) = inj₂ x
swap⊎ (inj₂ y) = inj₁ y



mutual
  lemFmap+ : {i : Size} → {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process+ i c₀)
             → (fmap+ (g ∘ f) P) ⊑+ (fmap+ g (fmap+ f P))
  lemFmap+ f g P .[] .nothing empty = empty
  lemFmap+ f g P .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (lemFmap∞ f g (PE P x) l m x₁)
  lemFmap+ f g P l m (intc .l .m x x₁) = intc l m x (lemFmap∞ f g (PI P x) l m x₁)
  lemFmap+ f g P .[] .(just (g (f (PT P x)))) (terc x) = terc x


  lemFmap∞ : {i : Size} → {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process∞  i c₀)
             → (fmap∞ (g ∘ f) P) ⊑∞  (fmap∞ g (fmap∞ f P))
  forcet (lemFmap∞ f g P l m x) = lemFmap f g (forcep P) l m (forcet x) 



  lemFmap : {i : Size} → {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process  i c₀)
             → (fmap (g ∘ f) P) ⊑  (fmap g (fmap f P))
  lemFmap f g (terminate x) l m x₁ = x₁
  lemFmap f g (node P) l m (tnode x) = tnode (lemFmap+ f g P l m x)



mutual 
 S⊓+ :  {i : Size} {c₀ c₁ : Choice} (P : Process+ i c₀) (Q : Process+ i c₁)
        →  (P ⊓+ Q) ⊑+ fmap+ swap⊎ ((Q ⊓+ P))
 S⊓+ P Q .[] .nothing empty = empty
 S⊓+ P Q .(Lab (Q ⊓+ P) _ ∷ l) m (extc l .m () x₁)
 S⊓+ P Q l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₂ x) (lemFmap∞ inj₁ swap⊎ (PI Q x) l m x₁)
 S⊓+ P Q l m (intc .l .m (inj₂ y) x₁) = intc l m (inj₁ y) (lemFmap∞ inj₂ swap⊎ (PI P y) l m x₁)
 S⊓+ P Q .[] .(just (swap⊎ (PT (Q ⊓+ P) _))) (terc ()) 




mutual 
 S⊓R+ :  {i : Size} {c₀ c₁ : Choice} (P : Process+ i c₀) (Q : Process+ i c₁)
        → (Q ⊓+ P) ⊑+ fmap+ swap⊎ ((P ⊓+ Q))
 S⊓R+ P Q .[] .nothing empty = empty
 S⊓R+ P Q .(Lab (P ⊓+ Q) _ ∷ l) m (extc l .m () x₁)
 S⊓R+ P Q l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₂ x) (lemFmap∞ inj₁ swap⊎ (PI P x) l m x₁)
 S⊓R+ P Q l m (intc .l .m (inj₂ y) x₁) = intc l m (inj₁ y) (lemFmap∞ inj₂ swap⊎ (PI Q y) l m x₁)
 S⊓R+ P Q .[] .(just (swap⊎ (PT (P ⊓+ Q) _))) (terc ())
