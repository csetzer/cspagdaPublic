module proofSymExt where 

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

swap⊎ : {c₀ c₁ : Choice} → ChoiceSet (c₀ ⊎' c₁) → ChoiceSet (c₁ ⊎' c₀)
swap⊎ (inj₁ x) = inj₂ x
swap⊎ (inj₂ y) = inj₁ y



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



mutual 
 S□+ :  {i : Size} {c₀ c₁ : Choice} (P : Process+ i c₀) (Q : Process+ i c₁)
        →  (P □++ Q) ⊑+ (fmap+ swap⊎ (Q □++ P))
 S□+ P Q .[] .nothing empty = empty
 S□+ P Q .(Lab Q x ∷ l) m (extc l .m (inj₁ x) x₁) = extc l m (inj₂ x) (lemFmap∞ inj₁ swap⊎ (PE Q x) l m x₁)
 S□+ P Q .(Lab P y ∷ l) m (extc l .m (inj₂ y) x₁) = extc l m (inj₁ y) (lemFmap∞ inj₂ swap⊎ (PE P y) l m x₁)
 S□+ P Q l m (intc .l .m (inj₁ x) x₁) =  intc l m (inj₂ x) (S□+∞ P (PI Q x) l m x₁)
 S□+ P Q l m (intc .l .m (inj₂ y) x₁) =  intc l m (inj₁ y) (S□∞+ (PI P y) Q l m x₁)
 S□+ P Q .[] .(just (inj₂ (PT Q x))) (terc (inj₁ x)) = terc (inj₂ x)
 S□+ P Q .[] .(just (inj₁ (PT P y))) (terc (inj₂ y)) = terc (inj₁ y)


 S□+∞  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process+ i c₀)
         → (Q : Process∞  i c₁)
         → Ref∞ {i}  (P □+∞+ Q) (fmap∞  swap⊎ {i} (Q □∞++ P))
 forcet (S□+∞ P Q l m x) =  tnode (S□+p P (forcep Q) l m (forcet' l m (forcet x)))
 
 S□+p  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process+ i c₀)
         → (Q : Process  i c₁)
         → Ref+ {i} (P □+p+ Q) (fmap+ swap⊎ {i} (Q □p++ P))
 S□+p P (terminate x) l m q = addTimeFmapLemma+ inj₂ swap⊎ P (inj₁ x) l m q
 S□+p P (node Q) l m q =  S□+ P Q l m q

-- goal  Tr+ l m (addTimed✓+ (inj₂ x) (fmap+ inj₁ P))
-- q   : Tr+ l m (fmap+ swap⊎ (addTimed✓+ (inj₁ x) (fmap+ inj₂ P)))

{-
 S□+p P (terminate x) .[] .nothing empty = empty
 S□+p P (terminate x) .(Lab P x₁ ∷ l) m (extc l .m x₁ x₂) = extc l m x₁ (lemFmap∞ inj₂ swap⊎ (PE P x₁) l m x₂)
 S□+p P (terminate x) l m (intc .l .m x₁ x₂) = intc l m x₁ {!xzb!}
 S□+p P (terminate x) .[] .(just (inj₂ x)) (terc (inj₁ x₁)) = terc (inj₁ x₁)
 S□+p P (terminate x) .[] .(just (inj₁ (PT P y))) (terc (inj₂ y)) = terc (inj₂ y)
 S□+p P (node Q) l m q =  S□+ P Q l m q

-}





 S□∞+  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process∞ i c₀)
         → (Q : Process+  i c₁)
         → Ref∞ {i}  (P □∞++ Q) (fmap∞  swap⊎ {i} (Q □+∞+ P))
 forcet (S□∞+ P Q l m x) = tnode (S□p+ (forcep P)  Q l m (forcet' l m (forcet x)))


 S□p+  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process i c₀)
         → (Q : Process+  i c₁)
         → Ref+ {i} (P □p++ Q) (fmap+ swap⊎ {i} (Q □+p+ P))
 S□p+ (terminate x) P l m q = addTimeFmapLemma+ inj₁ swap⊎ P (inj₂ x) l m q
 S□p+ (node Q) P l m q = S□+ Q P l m q


{-
 S□p+  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process i c₀)
         → (Q : Process+  i c₁)
         → Ref+ {i} (P □p++ Q) (fmap+ swap⊎ {i} (Q □+p+ P))
 S□p+ (terminate x) Q .[] .nothing empty = empty
 S□p+ (terminate x) Q .(Lab Q x₁ ∷ l) m (extc l .m x₁ x₂) = extc l m x₁ (lemFmap∞ inj₁ swap⊎ (PE Q x₁) l m x₂)
 S□p+ (terminate x) Q l m (intc .l .m x₁ x₂) = intc l m x₁ {!!}
 S□p+ (terminate x) Q .[] .(just (inj₁ x)) (terc (inj₁ x₁)) = terc (inj₁ x₁)
 S□p+ (terminate x) Q .[] .(just (inj₂ (PT Q y))) (terc (inj₂ y)) = terc (inj₂ y)
 S□p+ (node P) Q l m q =  S□+ P Q l m q
-}

--Goal for all : Tr∞ l m (PI (P □+p+ terminate x) x₁)

--Goal: Tr+ l m (addTimed✓+ (inj₁ x) (fmap+ inj₂ Q))
--x₂  : Tr∞ l m (fmap∞ swap⊎ (addTimed✓∞ (inj₂ x) (fmap∞ inj₁ (PI Q x₁))))

