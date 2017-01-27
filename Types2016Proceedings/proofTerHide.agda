module proofTerHide where 


open import process 
open import Size
open import choiceSetU
open import auxData
open import Data.Maybe
open import Data.List
open import Data.Sum
open import label
open import dataAuxFunction
open import renamingResult
open import TraceWithoutSize
open import RefWithoutSize
open import hidingOperator
open import primitiveProcess
open import Data.Bool
open import traceEquivalence
open import Data.Product


unitHideLaw : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Bool) 
               → (P : Process i c₀)
               → Hide A (terminate a)  ⊑ (terminate a)
unitHideLaw {i} {c₀} a A P l m q = q


unitHideLawᵣ : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Bool) 
               → (P : Process i c₀)
               →  (terminate a) ⊑ Hide A (terminate a)
unitHideLawᵣ {i} {c₀} a A P l m q = q


≡unitHide : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Bool) 
               → (P : Process i c₀)
        →  Hide A (terminate a) ≡ (terminate a)
≡unitHide a A P = (unitHideLaw a A P) , (unitHideLawᵣ a A P)




stopHideLaw : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Bool) 
               → (P : Process i c₀)
               → Hide A (STOP c₀)  ⊑ ((STOP c₀))
stopHideLaw {i} {c₀} a A (terminate x) .[] .nothing (tnode empty) = tnode empty
stopHideLaw {i} {c₀} a A (terminate x₁) .(efq _ ∷ l) m (tnode (extc l .m () x₂))
stopHideLaw {i} {c₀} a A (terminate x) l m (tnode (intc .l .m () x₂))
stopHideLaw {i} {c₀} a A (terminate x₁) .[] .(just (efq x)) (tnode (terc x)) = tnode (terc x)
stopHideLaw {i} {c₀} a A (node x) .[] .nothing (tnode empty) = tnode empty
stopHideLaw {i} {c₀} a A (node x₁) .(efq _ ∷ l) m (tnode (extc l .m () x₂))
stopHideLaw {i} {c₀} a A (node x) l m (tnode (intc .l .m () x₂))
stopHideLaw {i} {c₀} a A (node x₁) .[] .(just (efq x)) (tnode (terc x)) = tnode (terc x)


stopHideLawᵣ : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Bool) 
               → (P : Process i c₀)
               → (STOP c₀) ⊑  Hide A (STOP c₀)
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



≡stopHide : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Bool) 
               → (P : Process i c₀)
        →   Hide A (STOP c₀) ≡ (STOP c₀)
≡stopHide a A P = (stopHideLaw a A P) , (stopHideLawᵣ a A P) 
