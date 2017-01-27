module proofTerInter where 

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


TerIntLaw : {i : Size} {c₀ c₁  : Choice} (a : ChoiceSet c₀) (b : ChoiceSet c₁)
               → (terminate a ||| terminate b)  ⊑  terminate ((a ,, b))
TerIntLaw {i} {c₀} {c₁} a P l m q = q


TerIntLawᵣ : {i : Size} {c₀ c₁  : Choice} (a : ChoiceSet c₀) (b : ChoiceSet c₁)
               →   terminate ((a ,, b)) ⊑ (terminate a ||| terminate b)
TerIntLawᵣ {i} {c₀} {c₁} a P l m q = q


uniIntLaw₁ : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀) 
               → (P : Process i c₀)
               → (terminate a ||| P)  ⊑ fmap ((_,,_ a)) P
uniIntLaw₁ {i} {c₀} a P l m q = q
