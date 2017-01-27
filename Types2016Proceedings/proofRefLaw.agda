{-# OPTIONS --show-implicit #-}

module proofRefLaw where 

open import process 
open import Size
open import choiceSetU
open import Data.Maybe
open import Data.Product
open import label
open import Data.Product
open import TraceWithoutSize
open import RefWithoutSize
open import traceEquivalence
open import Data.Product
open import primitiveProcess


refl⊑ : {c : Choice} (P : Process ∞ c) → P ⊑ P 
refl⊑ {c} P l m x = x

trans⊑ : {c : Choice}(P : Process ∞ c)(Q : Process ∞ c)(R : Process ∞ c) → P ⊑ Q → Q ⊑ R → P ⊑ R 
trans⊑ {c} P Q R PQ QR l m tr = PQ l m (QR l m tr)

antiSym⊑ : {c₀ : Choice} → (P Q : Process ∞ c₀) → Set 
antiSym⊑ P Q = P ⊑ Q × Q ⊑ P

