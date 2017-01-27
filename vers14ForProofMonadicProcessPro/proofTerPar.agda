module proofTerPar where 

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
open import parallelSimple
open import restrict
open import Data.Bool

unit[] :  {i : Size} {c₀ : Choice} (a : ChoiceSet c₀)(P : Process i c₀) (A B : Label → Bool) 
        → (terminate a [ A ]||[ B ] P) ⊑ fmap ( (λ b → (a ,, b))) (P ↾ (B ∖ A))
unit[]  {i} {c₀} a P A B l m q =  q



unit[]r :  {i : Size} {c₀ : Choice} (a : ChoiceSet c₀)(P : Process i c₀) (A B : Label → Bool) 
        →  fmap ( (λ b → (a ,, b))) (P ↾ (B ∖ A)) ⊑ (terminate a [ A ]||[ B ] P)
unit[]r  {i} {c₀} a P A B l m q =  q



unit[]ᵣ :  {i : Size} {c₀ : Choice} (b : ChoiceSet c₀)(P : Process i c₀) (A B : Label → Bool) 
        → (P [ B ]||[ A ] terminate b) ⊑  fmap (λ a → (a ,, b))(P ↾ (B ∖ A))

unit[]ᵣ {i} {c₀} a (terminate x) A B l m q = q
unit[]ᵣ {i} {c₀} a (node x) A B l m (tnode x₁) = tnode x₁




unit[]ᵣᵣ :  {i : Size} {c₀ : Choice} (b : ChoiceSet c₀)(P : Process i c₀) (A B : Label → Bool) 
        →   fmap (λ a → (a ,, b))(P ↾ (B ∖ A)) ⊑ (P [ B ]||[ A ] terminate b)

unit[]ᵣᵣ {i} {c₀} a (terminate x) A B l m q = q
unit[]ᵣᵣ {i} {c₀} a (node x) A B l m (tnode x₁) = tnode x₁




ter[] :  {i : Size} {c₀ c₁ : Choice} (a : ChoiceSet c₀) (b : ChoiceSet c₁) (A  B : Label → Bool) 
        → (terminate a [ A ]||[ B ] terminate b) ⊑ fmap (λ x → a ,, b) (terminate ((a ,, b)))
ter[]  {i} {c₀} a P A B l m q =  q


ter[]ᵣ :  {i : Size} {c₀ c₁ : Choice} (a : ChoiceSet c₀) (b : ChoiceSet c₁) (A  B : Label → Bool) 
        →  fmap (λ x → a ,, b) (terminate ((a ,, b))) ⊑  (terminate a [ A ]||[ B ] terminate b)
ter[]ᵣ  {i} {c₀} a P A B l m q =  q
