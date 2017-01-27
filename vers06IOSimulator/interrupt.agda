module interrupt where

open import Size
open import process
open ∞Process
open import choiceSetU
open import choiceAuxFunction
open import dataAuxFunction
open import auxData
open import label
open import Data.String renaming (_++_ to _++s_)
open import showFunction
open import renamingResult 


mutual 
   Interrupt : (i : Size) →  {c₀ : Choice} → {c₁ : Choice} → ∞Process i (ChoiceSet c₀)  → ∞Process i (ChoiceSet c₁) → ∞Process i (((ChoiceSet c₀) +' (ChoiceSet c₁)) +' ((ChoiceSet c₀) × (ChoiceSet c₁))) 
   force (Interrupt i x y) j  =   Interrupt' j (force x j)  (force y j)

   Interrupt' : (i : Size) → {c₀ : Choice} → {c₁ : Choice} → Process i  (ChoiceSet c₀)  →  Process i (ChoiceSet c₁) → Process i (((ChoiceSet c₀) +' (ChoiceSet c₁)) +' ((ChoiceSet c₀) × (ChoiceSet c₁)))
   Interrupt' i (node E Lab PE I PI Stat)  (node E₁ Lab₁ PE₁ I₁ PI₁ Stat₁)  = node E' Lab' PE' I' PI' ( Stat ++s "△" ++s Stat₁ ) where
                                                   E' : Choice 
                                                   E' = E +'' E₁

                                                   I' : Choice
                                                   I' = I +'' I₁ 

                                                   Lab' :  ChoiceSet E' → Label
                                                   Lab' (inl x) = Lab x
                                                   Lab' (inr x) = Lab₁ x
                                           
                                                   PE'  : ChoiceSet E' → ∞Process i ((_ +' _) +' (_ × _))
                                                   force (PE' (inl x)) i  = Interrupt' i (force (PE x) i) (node E₁ Lab₁ PE₁ I₁ PI₁ Stat₁)
                                                   force (PE' (inr x)) i = fmap' i (inl ∘ inr) (force (PE₁ x) i)

                                                   PI' : ChoiceSet I' → ∞Process i ((_ +' _) +' (_ × _))    
                                                   force (PI' (inl x)) i = Interrupt' i (force (PI x) i) (node E₁ Lab₁ PE₁ I₁ PI₁ Stat₁)
                                                   force (PI' (inr x)) i = Interrupt' i (node E Lab PE I PI Stat) (force (PI₁ x) i)

   Interrupt' i (node _ _ _ _ _ _) (terminate x) = terminate (inl (inr x))
   Interrupt' i (terminate x) (node _ _ _ _ _ _) = terminate (inl (inl x))
   Interrupt' i (terminate x) (terminate x₁) = terminate (inr (x , x₁)) 
           

_△∞_ : {i : Size} →  {c₀ : Choice} → {c₁ : Choice} → ∞Process i  (ChoiceSet c₀)  → ∞Process i (ChoiceSet c₁) → ∞Process i (((ChoiceSet c₀) +' (ChoiceSet c₁)) +' ((ChoiceSet c₀) × (ChoiceSet c₁))) 
_△∞_ = Interrupt _


_△_ : {i : Size} → {c₀ : Choice} → {c₁ : Choice} → Process i  (ChoiceSet c₀)  →  Process i (ChoiceSet c₁) → Process i (((ChoiceSet c₀) +' (ChoiceSet c₁)) +' ((ChoiceSet c₀) × (ChoiceSet c₁)))
_△_ = Interrupt' _


infixl 10 _△∞_
infixl 10 _△_
