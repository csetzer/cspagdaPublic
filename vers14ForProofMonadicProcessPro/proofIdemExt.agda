module proofIdemExt where 

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
open import internalChoice



mutual
  Law₁₋₂ : {i : Size} {c₀  : Choice} (P : Process i c₀)
                 → (P □ P)  ⊑  fmap inj₁ P  
  Law₁₋₂ (terminate x) .[] .(just (inj₁ x)) (ter .(inj₁ x)) = {!!} -- is that correct ?
  Law₁₋₂ (terminate x) .[] .nothing (empty .(inj₁ x)) = tnode empty
  Law₁₋₂ (node x) l m tr = tnode (Law₁₋₂₊ x l m (forcet' l m tr))

  Law₁₋₂₊ : {i : Size} {c₀  : Choice} (P : Process+ i c₀)
                   → (P □+ P)  ⊑+  fmap+ inj₁ P  
  Law₁₋₂₊ p .[] .nothing empty = empty
  Law₁₋₂₊ p .(Lab p x ∷ l) m (extc l .m x x₁) = extc l m (inj₁ x) x₁
  Law₁₋₂₊ p l m (intc .l .m x x₁) = intc l m (inj₁ x) (Law₁₋₂∞+ p x l m x₁)
  Law₁₋₂₊ p .[] .(just (inj₁ (PT p x))) (terc x) = terc (inj₁ x)
  
  Law₁₋₂∞ : {i : Size} {c₀  : Choice} (P : Process∞ i c₀)
                → (P □∞∞ P)  ⊑∞  fmap∞ inj₁ P 
               
  forcet (Law₁₋₂∞ {i} {c₀} P l m q) = Law₁₋₂ (forcep P) l m (forcet q)

  Law₁₋₂∞+ : {i : Size} {c₀  : Choice} (P : Process+ i c₀)
                → (x   : ChoiceSet (I P))
                → ((PI P x) □∞+ P)  ⊑∞  (fmap∞ inj₁ (PI P x)) 
               
  forcet (Law₁₋₂∞+ {i} {c₀} P x l m q) {j} = {!!}







{-

mutual
  Law₁₋₂' : {i : Size} {c₀  : Choice} (P : Process i c₀) → (P □ P)  ⊑  fmap {!!} P  
  Law₁₋₂' P l m q = {!!} 

  Law₁₋₂₊' : {i : Size} {c₀  : Choice} (P : Process+ i c₀) → (P □+ P)  ⊑+  fmap+ inj₁ P  
  Law₁₋₂₊' p l m tr = {!!}
  
  Law₁₋₂∞' : {i : Size} {c₀  : Choice} (P : Process∞ i c₀) → (P □∞∞ P)  ⊑∞  fmap∞ inj₁ P 
  forcet (Law₁₋₂∞' {i} {c₀} P l m q) = {!!} --

  Law₁₋₂∞+' : {i : Size} {c₀  : Choice} (P : Process+ i c₀) → (x   : ChoiceSet (I P))
                → ((PI P x) □∞+ P)  ⊑∞  (fmap∞ inj₁ (PI P x)) 
               
  forcet (Law₁₋₂∞+' {i} {c₀} P x l m q) {j} = {!!}

unify : {c : Choice} → ChoiceSet (c ⊎' c)  → ChoiceSet c
unify (inj₁ x) = x
unify (inj₂ y) = y



lem : {c : Choice} → ChoiceSet (c ⊎' c)  → ChoiceSet c
lem (inj₁ x) = x
lem (inj₂ y) = y


-}





--Law₁₋₂ {!!} l m {!!}
--node {j} P
-- → fmap+ lem (P □+ P)  ⊑+  P


{-


  Law₁₋₂' : {i : Size} {c₀  : Choice} (P : Process i c₀)
                 →  fmap inj₁ P ⊑ (P □ P)
  Law₁₋₂' P l m tr = {!!}


lemBind : (i : Size)(c : Choice)(x : ChoiceSet c)
                     →  Tr [] (just (inj₁ x)) (2-✓ x x)
lemBind i c x = {!!}
mutual 
 I□+ :  {i : Size} {c₀ : Choice} (P : Process+ i c₀)
        →  (P □++ P) ⊑+ fmap+ inj₁ P
 I□+ P .[] .nothing empty = empty
 I□+ P .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m (inj₁ x) x₁
 I□+ P l (just (inj₁ x)) (intc .l .(just (inj₁ x)) x₁ x₂) = intc l (just (inj₁ x)) {!!} (I□+' {!P!} l (just (inj₁ x)) {!!}) -- intc l (just (inj₁ x)) {!!} x₂
 I□+ P l (just (inj₂ y)) (intc .l .(just (inj₂ y)) x₁ x₂) = {!!} -- intc l (just (inj₂ y)) {!!} x₂
 I□+ P l nothing (intc .l .nothing x x₁) = intc l nothing  (inj₁ x) {!!}  --  intc l m (inj₁ x) {!!} -- (S+ P x l m x₁)
 I□+ P .[] .(just (inj₁ (PT P x))) (terc x) = terc (inj₁ x)

 I□+' :  {i : Size} {c₀ : Choice} (P : Process∞ i c₀)
        →  (P □∞∞ P) ⊑∞ fmap∞ inj₁ P
 I□+' = {!!}
 -}






