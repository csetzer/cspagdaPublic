module proofTerHide where 

open import process 
open import indTr
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
open import refinement
open import dataAuxFunction
open import hidingOperator
open import primitiveProcess
open import Data.Bool


unitHideLaw₁ : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Bool) 
               → (P : Process i c₀)
               → Hide A (terminate a)  ⊑ fmap (λ x → x) (terminate a)
unitHideLaw₁ {i} {c₀} a A P l m q = q


unitHideLawᵣ : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Bool) 
               → (P : Process i c₀)
               →  fmap (λ x → x) (terminate a) ⊑ Hide A (terminate a)
unitHideLawᵣ {i} {c₀} a A P l m q = q


stopHideLaw₁ : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Bool) 
               → (P : Process i c₀)
               → Hide A (STOP c₀)  ⊑ fmap (λ x → x) ((STOP c₀))
stopHideLaw₁ {i} {c₀} a A (terminate x) .[] .nothing (tnode empty) = tnode empty
stopHideLaw₁ {i} {c₀} a A (terminate x₁) .(efq _ ∷ l) m (tnode (extc l .m () x₂))
stopHideLaw₁ {i} {c₀} a A (terminate x) l m (tnode (intc .l .m () x₂))
stopHideLaw₁ {i} {c₀} a A (terminate x₁) .[] .(just (efq x)) (tnode (terc x)) = tnode (terc x)
stopHideLaw₁ {i} {c₀} a A (node x) .[] .nothing (tnode empty) = tnode empty
stopHideLaw₁ {i} {c₀} a A (node x₁) .(efq _ ∷ l) m (tnode (extc l .m () x₂))
stopHideLaw₁ {i} {c₀} a A (node x) l m (tnode (intc .l .m () x₂))
stopHideLaw₁ {i} {c₀} a A (node x₁) .[] .(just (efq x)) (tnode (terc x)) = tnode (terc x)


stopHideLawᵣ : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Bool) 
               → (P : Process i c₀)
               → fmap (λ x → x) ((STOP c₀))  ⊑  Hide A (STOP c₀)
stopHideLawᵣ {i} {c₀} a A (terminate x) .[] .nothing (tnode empty) = tnode empty
stopHideLawᵣ {i} {c₀} a A (terminate x₁) .(efq _ ∷ l) m (tnode (extc l .m (sub () x) x₂))
stopHideLawᵣ {i} {c₀} a A (terminate x) l m (tnode (intc .l .m (inj₁ ()) x₂))
stopHideLawᵣ {i} {c₀} a A (terminate x) l m (tnode (intc .l .m (inj₂ (sub () x₁)) x₂))
stopHideLawᵣ {i} {c₀} a A (terminate x₁) .[] .(just (efq x)) (tnode (terc x)) = tnode (terc x)
stopHideLawᵣ {i} {c₀} a A (node x) .[] .nothing (tnode empty) = tnode empty
stopHideLawᵣ {i} {c₀} a A (node x₁) .(efq _ ∷ l) m (tnode (extc l .m (sub () x) x₂))
stopHideLawᵣ {i} {c₀} a A (node x) l m (tnode (intc .l .m (inj₁ ()) x₂))
stopHideLawᵣ {i} {c₀} a A (node x) l m (tnode (intc .l .m (inj₂ (sub () x₁)) x₂))
stopHideLawᵣ {i} {c₀} a A (node x₁) .[] .(just (efq x)) (tnode (terc x)) = tnode (terc x) 



