module proofIdemInte where

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


mutual 
 I⊓+ :  {i : Size} {c₀ : Choice} (P : Process+ i c₀)
        →  fmap+ inj₁  P ⊑+ (P ⊓+ P)
 I⊓+ P .[] .nothing empty = empty
 I⊓+ P .(Lab (P ⊓+ P) _ ∷ l) m (extc l .m () x₁)
 I⊓+ P l m (intc .l .m (inj₁ x) x₁) = intc l m x x₁
 I⊓+ P l m (intc .l .m (inj₂ y) x₁) = {!!}
 I⊓+ P .[] .(just (PT (P ⊓+ P) _)) (terc ())





{-
mutual 
 I⊓R+ :  {i : Size} {c₀ : Choice} (P : Process+ i c₀)
        →  (P ⊓+ P)  ⊑+ fmap+ inj₁ P
 I⊓R+ P l m tr = {!tr!}

U⊎ : {c : Choice} → ChoiceSet (c ⊎' c) → ChoiceSet c 
U⊎ (inj₁ x) = x
U⊎ (inj₂ y) = y


U⊎' : {c : Choice} → ChoiceSet c  → ChoiceSet (c ⊎' c)
U⊎' x =  {!!} 
-}



