module proofAss where 

open import process

open import TraceWithoutSize
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
open import RefWithoutSize
open import dataAuxFunction


Ass× : {c₀ c₁ c₂ : Choice} → ChoiceSet (c₀ ×' (c₁ ×' c₂))  → ChoiceSet ((c₀ ×' c₁) ×' c₂) 
Ass× (x ,, (x₁ ,, x₂)) = ((x ,, x₁) ,, x₂)

Ass×' : {c₀ c₁ c₂ : Choice} → ChoiceSet ((c₀ ×' c₁) ×' c₂)  → ChoiceSet (c₀ ×' (c₁ ×' c₂)) 
Ass×' ((x ,, x₁) ,, x₂) = x ,, (x₁ ,, x₂) 

mutual
  lemFmap+ : {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process+ ∞ c₀)
             → (fmap+ (g ∘ f) P) ⊑+ (fmap+ g (fmap+ f P))
  lemFmap+ f g P .[] .nothing empty = empty
  lemFmap+ f g P .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (lemFmap∞ f g (PE P x) l m x₁)
  lemFmap+ f g P l m (intc .l .m x x₁) = intc l m x (lemFmap∞ f g (PI P x) l m x₁)
  lemFmap+ f g P .[] .(just (g (f (PT P x)))) (terc x) = terc x



  lemFmap∞ : {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process∞  ∞ c₀)
             → (fmap∞ (g ∘ f) P) ⊑∞  (fmap∞ g (fmap∞ f P))
  forcet (lemFmap∞ f g P l m x) = lemFmap f g (forcep P) l m (forcet x) 





  lemFmap : {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process  ∞ c₀)
             → (fmap (g ∘ f) P) ⊑  (fmap g (fmap f P))
  lemFmap f g (terminate x) l m x₁ = x₁
  lemFmap f g (node P) l m (tnode x) = tnode (lemFmap+ f g P l m x)






mutual
  lemFmap+R : {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process+ ∞ c₀)
             → (fmap+ g (fmap+ f P)) ⊑+ (fmap+ (g ∘ f) P)
  lemFmap+R f g P .[] .nothing empty = empty
  lemFmap+R f g P .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (lemFmap∞R f g (PE P x) l m x₁) 
  lemFmap+R f g P l m (intc .l .m x x₁) = intc l m x (lemFmap∞R f g (PI P x) l m x₁) 
  lemFmap+R f g P .[] .(just (g (f (PT P x)))) (terc x) = terc x


  lemFmap∞R :  {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process∞  ∞ c₀)
             → (fmap∞ g (fmap∞ f P)) ⊑∞  (fmap∞ (g ∘ f) P)
  forcet (lemFmap∞R f g P l m x) = lemFmapR f g (forcep P) l m (forcet x) 


  lemFmapR : {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process  ∞ c₀)
             → (fmap g (fmap f P)) ⊑  (fmap (g ∘ f) P)
  lemFmapR f g (terminate x) l m x₁ = x₁
  lemFmapR f g (node P) l m (tnode x) = tnode (lemFmap+R f g P l m x)





mutual 
 S|||+' : {c₀ c₁ c₂ : Choice}  (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁) (Z : Process+ ∞ c₂)
        →  ((P |||++ Q) |||++ Z) ⊑+ fmap+ Ass× (P |||++ (Q  |||++ Z ))
 S|||+' {c₀} {c₁} {c₂} P Q Z .[] .nothing empty = empty
 S|||+' {c₀} {c₁} {c₂} P Q Z .(Lab P x ∷ l) m (extc l .m (inj₁ x) x₁) = extc l m (inj₁ (inj₁ x)) (S|||∞++ (PE P x) Q Z l m x₁)
 S|||+' {c₀} {c₁} {c₂} P Q Z .(Lab Q x ∷ l) m (extc l .m (inj₂ (inj₁ x)) x₁) = extc l m (inj₁ (inj₂ x)) (S|||+∞+ P (PE Q x) Z l m x₁)
 S|||+' {c₀} {c₁} {c₂} P Q Z .(Lab Z y ∷ l) m (extc l .m (inj₂ (inj₂ y)) x₁) = extc l m (inj₂ y) (S|||++∞ P Q (PE Z y) l m x₁)
 S|||+' {c₀} {c₁} {c₂} P Q Z l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₁ (inj₁ x)) (S|||∞++ (PI P x) Q Z l m x₁)
 S|||+' {c₀} {c₁} {c₂} P Q Z l m (intc .l .m (inj₂ (inj₁ x)) x₁) = intc l m (inj₁ (inj₂ x)) (S|||+∞+ P (PI Q x) Z l m x₁)
 S|||+' {c₀} {c₁} {c₂} P Q Z l m (intc .l .m (inj₂ (inj₂ y)) x₁) = intc l m (inj₂ y) (S|||++∞ P Q (PI Z y) l m x₁)
 S|||+' {c₀} {c₁} {c₂} P Q Z .[] .(just ((PT P x ,, PT Q x₁) ,, PT Z x₂)) (terc (x ,, (x₁ ,, x₂))) = terc ((x ,, x₁) ,, x₂)

 S|||∞++  : {c₀ c₁ c₂ : Choice} (P : Process∞ ∞ c₀) (Q : Process+  ∞ c₁) (Z : Process+ ∞ c₂)
         → Ref∞  (((P |||∞+ Q) |||∞+ Z)) (fmap∞ Ass× ( P |||∞+ (Q |||++ Z)))
 forcet (S|||∞++ {c₀} {c₁} {c₂} P Q Z l m x) = tnode (S|||+pp (forcep P) Q Z l m (forcet' l m (forcet x)))

 S|||+∞+  : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀) (Q : Process∞ ∞ c₁) (Z : Process+ ∞ c₂)
         → Ref∞ (((P |||+∞ Q) |||∞+ Z)) (fmap∞ Ass× ( P |||+∞ (Q |||∞+ Z)))
 forcet (S|||+∞+ {c₀} {c₁} {c₂} P Q Z l m x) = tnode (S|||p+p P (forcep Q) Z l m (forcet' l m (forcet x)))

 S|||++∞  : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀) (Q : Process+  ∞ c₁) (Z : Process∞ ∞ c₂)
         → Ref∞ (((P |||++ Q) |||+∞ Z)) (fmap∞ Ass× ( P |||+∞ (Q |||+∞ Z)))
 forcet (S|||++∞ {c₀} {c₁} {c₂} P Q Z l m x)  = tnode (S|||pp+ P Q (forcep Z) l m (forcet' l m (forcet x)))


 S|||+pp  : {c₀ c₁ c₂ : Choice}(P : Process ∞ c₀)(Q : Process+ ∞ c₁)(Z : Process+ ∞ c₂)
         →  Ref+ (((P |||p+ Q) |||++ Z)) (fmap+ Ass× ( P |||p+ (Q |||++ Z)))
 S|||+pp (terminate x) Q Z l m tr = {!!}
 S|||+pp (node x) Q Z l m tr = S|||+' x Q Z l m tr

 S|||+pp'  : {c₀ c₁ c₂ : Choice}(P : Process ∞ c₀)(Q : Process+ ∞ c₁)(Z : Process+ ∞ c₂)
         → (x   : ChoiceSet c₀) → (x₁  : ChoiceSet (E Q))
         → (l : List Label)
         → (m : Maybe ((ChoiceSet c₀ auxData.× ChoiceSet c₁) auxData.× ChoiceSet c₂))
         → (x₂  : Tr∞ l m (fmap∞ Ass× (fmap∞ (_,,_ x) (PE Q x₁ |||∞+ Z))))
         →  Tr∞ l m (fmap∞ (_,,_ x) (PE Q x₁) |||∞+ Z)
 forcet (S|||+pp' (terminate x) Q Z x₁ x₂ l m x₃) = {!!}
 forcet (S|||+pp' (node x) Q Z x₁ x₂ l m x₃) =  {!!}



 S|||p+p  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)(Q : Process ∞ c₁)(Z : Process+ ∞ c₂)
         →  Ref+  (((P |||+p Q) |||++ Z)) (fmap+ Ass× ( P |||++ (Q |||p+ Z)))
 S|||p+p P (terminate x) Z l m tr = {!!}
 S|||p+p P (node x) Z l m tr = S|||+' P x Z l m tr


 S|||pp+  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)(Q : Process+ ∞ c₁)(Z : Process ∞ c₂)
         →  Ref+ (((P |||++ Q) |||+p Z)) (fmap+ Ass× ( P |||++ (Q |||+p Z)))
 S|||pp+ P Q (terminate x) l m tr = {!!}
 S|||pp+ P Q (node x) l m tr = S|||+' P Q x  l m tr





{-
 S|||+pp (terminate x) Q Z .(Lab Q x₁ ∷ l) m (extc l .m (inj₁ x₁) x₂) = extc l m (inj₁ x₁) {!!} -- (S|||+pp' (terminate x) Q Z x x₁ l m x₂)
 S|||+pp (terminate x) Q Z .(Lab Z y ∷ l) m (extc l .m (inj₂ y) x₂) = extc l m (inj₂ y) {!!}
 S|||+pp (terminate x) Q Z l m (intc .l .m (inj₁ x₁) x₂) = intc l m (inj₁ x₁) {!!}
 S|||+pp (terminate x) Q Z l m (intc .l .m (inj₂ y) x₂) = intc l m (inj₂ y) {!!}



 S|||+pp'  : {c₀ c₁ c₂ : Choice}(P : Process ∞ c₀)(Q : Process+ ∞ c₁)(Z : Process+ ∞ c₂)
         → (x   : ChoiceSet c₀) → (x₁  : ChoiceSet (E Q))
         → (l : List Label)
         → (m : Maybe ((ChoiceSet c₀ auxData.× ChoiceSet c₁) auxData.× ChoiceSet c₂))
         → (x₂  : Tr∞ l m (fmap∞ Ass× (fmap∞ (_,,_ x) (PE Q x₁ |||∞+ Z))))
         →  Tr∞ l m (fmap∞ (_,,_ x) (PE Q x₁) |||∞+ Z)
 forcet (S|||+pp' (terminate x) Q Z x₁ x₂ l m x₃) = {!lemFmapR!}
 forcet (S|||+pp' (node x) Q Z x₁ x₂ l m x₃) =  {!!}




-}

















