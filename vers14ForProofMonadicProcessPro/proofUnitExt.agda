module proofUnitExt where 

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
open import primitiveProcess



mutual
  lemFmap+ : {i : Size} → {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process+ i c₀)
             → (fmap+ (g ∘ f) P) ⊑+ (fmap+ g (fmap+ f P))
  lemFmap+ f g P .[] .nothing empty = empty
  lemFmap+ f g P .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (lemFmap∞ f g (PE P x) l m x₁)
  lemFmap+ f g P l m (intc .l .m x x₁) = intc l m x (lemFmap∞ f g (PI P x) l m x₁)
  lemFmap+ f g P .[] .(just (g (f (PT P x)))) (terc x) = terc x


  lemFmap∞ : {i : Size} → {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process∞  i c₀)
             → (fmap∞ (g ∘ f) P) ⊑∞  (fmap∞ g (fmap∞ f P))
  forcet (lemFmap∞ f g P l m x) = lemFmap f g (forcep P) l m (forcet x) 



  lemFmap : {i : Size} → {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process  i c₀)
             → (fmap (g ∘ f) P) ⊑  (fmap g (fmap f P))
  lemFmap f g (terminate x) l m x₁ = x₁
  lemFmap f g (node P) l m (tnode x) = tnode (lemFmap+ f g P l m x)



mutual
  addTimeFmapLemma+ : {i : Size} {c₀ c₁ c₂ : Choice} 
                     (f : ChoiceSet c₀ → ChoiceSet c₁) 
                     (g : ChoiceSet c₁ → ChoiceSet c₂) 
                     (P : Process+ i c₀)
                     (a : ChoiceSet c₁)
                     → addTimed✓+ (g a) (fmap+ (g ∘ f) P) ⊑+ fmap+ g (addTimed✓+ a (fmap+ f P))
  addTimeFmapLemma+ {i} {c₀} {c₁} {c₂} f g P a .[] .nothing empty = empty
  addTimeFmapLemma+ {i} {c₀} {c₁} {c₂} f g P a .(Lab P x ∷ l) m (extc l .m x q) = extc l m x (lemFmap∞ f g (PE P x) l m q)
  addTimeFmapLemma+ {i} {c₀} {c₁} {c₂} f g P a l m (intc .l .m x q) = intc l m x (addTimeFmapLemma∞ f g (PI P x) a l m q)
  addTimeFmapLemma+ {i} {c₀} {c₁} {c₂} f g P a .[] .(just (g a)) (terc (inj₁ x)) = terc (inj₁ x)
  addTimeFmapLemma+ {i} {c₀} {c₁} {c₂} f g P a .[] .(just (g (f (PT P y)))) (terc (inj₂ y)) = terc (inj₂ y) 


  addTimeFmapLemma∞ : {i : Size} {c₀ c₁ c₂ : Choice} 
                     (f : ChoiceSet c₀ → ChoiceSet c₁) 
                     (g : ChoiceSet c₁ → ChoiceSet c₂) 
                     (P : Process∞  i c₀)
                     (a : ChoiceSet c₁)
                     → addTimed✓∞ (g a) (fmap∞ (g ∘ f) P) ⊑∞ fmap∞ g (addTimed✓∞ a (fmap∞ f P))
  forcet (addTimeFmapLemma∞ {i} {c₀} {c₁} {c₂} f g P a l m q) = addTimeFmapLemma f g (forcep P) a l m (forcet q)


  addTimeFmapLemma : {i : Size} {c₀ c₁ c₂ : Choice} 
                     (f : ChoiceSet c₀ → ChoiceSet c₁) 
                     (g : ChoiceSet c₁ → ChoiceSet c₂) 
                     (P : Process  i c₀)
                     (a : ChoiceSet c₁)
                     → addTimed✓ (g a) (fmap (g ∘ f) P) ⊑ fmap g (addTimed✓ a (fmap f P))
  addTimeFmapLemma {i} {c₀} {c₁} {c₂} f g (terminate x) a .[] .nothing (tnode empty) = tnode empty
  addTimeFmapLemma {i} {c₀} {c₁} {c₂} f g (terminate x) a .(efq _ ∷ l) m (tnode (extc l .m () x₂))
  addTimeFmapLemma {i} {c₀} {c₁} {c₂} f g (terminate x) a l m (tnode (intc .l .m () x₂))
  addTimeFmapLemma {i} {c₀} {c₁} {c₂} f g (terminate x) a .[] .(just (g a)) (tnode (terc zero)) = tnode (terc zero)
  addTimeFmapLemma {i} {c₀} {c₁} {c₂} f g (terminate x) a .[] .(just (g (f x))) (tnode (terc (suc zero))) = (tnode (terc (suc zero)))
  addTimeFmapLemma {i} {c₀} {c₁} {c₂} f g (terminate x) a .[] .(just (g (unifyA⊎A (if suc (suc _) then inj₁ a else (inj₂ (f x)))))) (tnode (terc (suc (suc ()))))
  addTimeFmapLemma {i} {c₀} {c₁} {c₂} f g (node P) a l m (tnode q) = tnode (addTimeFmapLemma+ f g P a l m q)

 --addTimeFmapLemma {!(terminate x)!} {!(terminate x)!} ? x l m tr



mutual
  UnitLawEx₁₋₂ : {i : Size} {c₀ c₁ : Choice} (P : Process i c₀)
                 → (P □ STOP c₁  )  ⊑  fmap inj₁ P  
  UnitLawEx₁₋₂ {i} {c₀} {c₁} (terminate x) l m tr = {!!}
  UnitLawEx₁₋₂ (node x) l m tr =  tnode (UnitLawEx₁₋₂+ x l m (forcet' l m tr))

  UnitLawEx₁₋₂+ : {i : Size} {c₀ c₁ : Choice} (P : Process+ i c₀)
                 → (P □+ STOP+ c₁  )  ⊑+  fmap+ inj₁ P  
  UnitLawEx₁₋₂+ P .[] .nothing empty = empty
  UnitLawEx₁₋₂+ P .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m (inj₁ x) x₁
  UnitLawEx₁₋₂+ P l m (intc .l .m x x₁) = intc l m (inj₁ x) (UnitLawEx₁₋₂∞+ (PI P x) l m x₁)
  UnitLawEx₁₋₂+ P .[] .(just (inj₁ (PT P x))) (terc x) = terc (inj₁ x)

  UnitLawEx₁₋₂∞ : {i : Size} {c₀ c₁ : Choice} (P : Process∞ i c₀)
                 → (P □∞∞ STOP∞ c₁  )  ⊑∞  fmap∞ inj₁ P  
  forcet (UnitLawEx₁₋₂∞ P l m tr) = UnitLawEx₁₋₂ (forcep P) l m (forcet tr)

  UnitLawEx₁₋₂∞+ : {i : Size} {c₀ c₁ : Choice} (P : Process∞ i c₀)
                 → (P □∞+ STOP+ c₁  )  ⊑∞  fmap∞ inj₁ P  
  forcet (UnitLawEx₁₋₂∞+ {i} {c₀} {c₁} P l m tr) {j} = {!!} -- UnitLawEx₁₋₂ (forcep {i} {!P!}) l m (forcet tr)











mutual
  UnitLawExR₁₋₂ : {i : Size} {c₀ c₁ : Choice} (P : Process i c₀)
                 →  fmap inj₁ P    ⊑ (P □ STOP c₁  )
  UnitLawExR₁₋₂ {i} {c₀} {c₁} (terminate x) l m (tnode x₁) = {!!}
  UnitLawExR₁₋₂ (node x) l m tr = tnode (UnitLawExR₁₋₂+ x l m (forcet' l m tr))

  UnitLawExR₁₋₂+ : {i : Size} {c₀ c₁ : Choice} (P : Process+ i c₀)
                 →   fmap+ inj₁ P   ⊑+ (P □+ STOP+ c₁)
  UnitLawExR₁₋₂+ P .[] .nothing empty = empty
  UnitLawExR₁₋₂+ P .(Lab P x ∷ l) m (extc l .m (inj₁ x) x₁) = extc l m x x₁
  UnitLawExR₁₋₂+ P .(efq _ ∷ l) m (extc l .m (inj₂ ()) x₁)
  UnitLawExR₁₋₂+ P l m (intc .l .m (inj₁ x) x₁) = intc l m x (UnitLawExR₁₋₂∞+ (PI P x) l m x₁)
  UnitLawExR₁₋₂+ P l m (intc .l .m (inj₂ ()) x₁)
  UnitLawExR₁₋₂+ P .[] .(just (inj₁ (PT P x))) (terc (inj₁ x)) = terc x
  UnitLawExR₁₋₂+ P .[] .(just (inj₂ (efq _))) (terc (inj₂ ()))
  UnitLawExR₁₋₂∞ : {i : Size} {c₀ c₁ : Choice} (P : Process∞ i c₀)
                 →  fmap∞ inj₁ P    ⊑∞ (P □∞∞ STOP∞ c₁  )
  forcet (UnitLawExR₁₋₂∞ P l m tr) = UnitLawExR₁₋₂ (forcep P) l m (forcet tr)

  UnitLawExR₁₋₂∞+ : {i : Size} {c₀ c₁ : Choice} (P : Process∞ i c₀)
                 →  fmap∞ inj₁ P     ⊑∞  (P □∞+ STOP+ c₁  )
  forcet (UnitLawExR₁₋₂∞+ {i} {c₀} {c₁} P l m tr) {j} = {!!} -- UnitLawExR₁₋₂p+ (forcep P) l m (forcet {↑ j} {!!})




{-
  UnitLawExR₁₋₂p+ : {i : Size} {c₀ c₁ : Choice} (P : Process i c₀)
                 →  fmap inj₁ P     ⊑  (P □p+ STOP+ c₁ )
  UnitLawExR₁₋₂p+ {i} {c₀} {c₁} P l m tr = UnitLawExR₁₋₂ P l m {!!} 
-}

