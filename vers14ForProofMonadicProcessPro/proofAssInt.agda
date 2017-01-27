module proofAssInt where 

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


Ass× : {c₀ c₁ c₂ : Choice} → ChoiceSet (c₀ ×' (c₁ ×' c₂))  → ChoiceSet ((c₀ ×' c₁) ×' c₂) 
Ass× (x ,, (x₁ ,, x₂)) = ((x ,, x₁) ,, x₂)

Ass×' : {c₀ c₁ c₂ : Choice} → ChoiceSet ((c₀ ×' c₁) ×' c₂)  → ChoiceSet (c₀ ×' (c₁ ×' c₂)) 
Ass×' ((x ,, x₁) ,, x₂) = x ,, (x₁ ,, x₂) 


-- Tr+ l m (fmap+ (_,,_ x) Q |||++ Z)
-- Tr+ l m (fmap+ (_,,_ x) Q)




mutual 
 S|||+' :  {i : Size} {c₀ c₁ c₂ : Choice}  (P : Process+ i c₀) (Q : Process+ i c₁) (Z : Process+ i c₂)
        →  ((P |||++ Q) |||++ Z) ⊑+ fmap+ Ass× (P |||++ (Q  |||++ Z ))
 S|||+' {i} {c₀} {c₁} {c₂} P Q Z .[] .nothing empty = empty
 S|||+' {i} {c₀} {c₁} {c₂} P Q Z .(Lab P x ∷ l) m (extc l .m (inj₁ x) x₁) = extc l m (inj₁ (inj₁ x)) (S|||∞++ (PE P x) Q Z l m x₁)
 S|||+' {i} {c₀} {c₁} {c₂} P Q Z .(Lab Q x ∷ l) m (extc l .m (inj₂ (inj₁ x)) x₁) = extc l m (inj₁ (inj₂ x)) (S|||+∞+ P (PE Q x) Z l m x₁)
 S|||+' {i} {c₀} {c₁} {c₂} P Q Z .(Lab Z y ∷ l) m (extc l .m (inj₂ (inj₂ y)) x₁) = extc l m (inj₂ y) (S|||++∞ P Q (PE Z y) l m x₁)
 S|||+' {i} {c₀} {c₁} {c₂} P Q Z l m (intc .l .m (inj₁ x) x₁)        = intc l m (inj₁ (inj₁ x)) (S|||∞++ (PI P x) Q Z l m x₁)
 S|||+' {i} {c₀} {c₁} {c₂} P Q Z l m (intc .l .m (inj₂ (inj₁ x)) x₁) = intc l m (inj₁ (inj₂ x)) (S|||+∞+ P (PI Q x) Z l m x₁)
 S|||+' {i} {c₀} {c₁} {c₂} P Q Z l m (intc .l .m (inj₂ (inj₂ y)) x₁) = intc l m (inj₂ y) (S|||++∞ P Q (PI Z y) l m x₁)
 S|||+' {i} {c₀} {c₁} {c₂} P Q Z .[] .(just ((PT P x ,, PT Q x₁) ,, PT Z x₂)) (terc (x ,, (x₁ ,, x₂))) = terc ((x ,, x₁) ,, x₂)

 S|||∞++  : {i : Size} {c₀ c₁ c₂ : Choice} (P : Process∞ i c₀) (Q : Process+  i c₁) (Z : Process+ i c₂)
         → Ref∞ {i} (((P |||∞+ Q) |||∞+ Z)) (fmap∞ Ass× ( P |||∞+ (Q |||++ Z)))
 forcet (S|||∞++ {i} {c₀} {c₁} {c₂} P Q Z l m x) {j} = {!!} -- tnode (S|||+pp (forcep P) Q Z l m (forcet' l m {!!}))

 S|||+∞+  : {i : Size} {c₀ c₁ c₂ : Choice} (P : Process+ i c₀) (Q : Process∞  i c₁) (Z : Process+ i c₂)
         → Ref∞ {i} (((P |||+∞ Q) |||∞+ Z)) (fmap∞ Ass× ( P |||+∞ (Q |||∞+ Z)))
 forcet (S|||+∞+ {i} {c₀} {c₁} {c₂} P Q Z l m x) {j} = {!!} -- tnode (S|||p+p P (forcep Q) Z l m (forcet' l m (forcet x)))

 S|||++∞  : {i : Size} {c₀ c₁ c₂ : Choice} (P : Process+ i c₀) (Q : Process+  i c₁) (Z : Process∞ i c₂)
         → Ref∞ {i} (((P |||++ Q) |||+∞ Z)) (fmap∞ Ass× ( P |||+∞ (Q |||+∞ Z)))
 forcet (S|||++∞ {i} {c₀} {c₁} {c₂} P Q Z l m x)  = {!!} -- tnode (S|||pp+ P Q (forcep {!!}) l m (forcet' l m (forcet {!x!})))

{-
 S|||+∞+'  : {i i' i'' : Size} {c₀ c₁ c₂ : Choice} (P : Process+ i c₀) (Q : Process∞  i' c₁) (Z : Process+ i'' c₂)
         → Ref∞  {!!}  {!!} -- (((P |||+∞ Q) |||∞+ Z)) (fmap∞ Ass× ( P |||+∞ (Q |||∞+ Z)))
 forcet (S|||+∞+' {i} {c₀} {c₁} {c₂} P Q Z l m x) {j} = {!!} -- tnode (S|||p+p P (forcep Q) Z l m (forcet' l m (forcet x)))
-}


{-
 S|||+pp  : {i : Size} → {c₀ c₁ c₂ : Choice}(P : Process i c₀)(Q : Process+ i c₁)(Z : Process+ i c₂)
         →  Ref+ {i} (((P |||p+ Q) |||++ Z)) (fmap+ Ass× ( P |||p+ (Q |||++ Z)))
 S|||+pp (terminate x) Q Z l m tr = {!!}
 S|||+pp (node x) Q Z l m tr = S|||+' x Q Z l m tr
-}

{-
 S|||p+p  : {i : Size} → {c₀ c₁ c₂ : Choice}(P : Process+ i c₀)(Q : Process i c₁)(Z : Process+ i c₂)
         →  Ref+ {i} (((P |||+p Q) |||++ Z)) (fmap+ Ass× ( P |||++ (Q |||p+ Z)))
 S|||p+p P (terminate x) Z l m tr = {!!}
 S|||p+p P (node x) Z l m tr = S|||+' P x Z l m tr
-}

{-
 S|||pp+  : {i : Size} → {c₀ c₁ c₂ : Choice}(P : Process+ i c₀)(Q : Process+ i c₁)(Z : Process i c₂)
         →  Ref+ {i} (((P |||++ Q) |||+p Z)) (fmap+ Ass× ( P |||++ (Q |||+p Z)))
 S|||pp+ P Q (terminate x) l m tr = {!!}
 S|||pp+ P Q (node x) l m tr = S|||+' P Q x  l m tr
-}




















