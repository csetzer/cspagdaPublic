module lemFmap where 

open import process 
open import Size
open import choiceSetU
open import auxData
open import Data.Maybe
open import Data.Product
open import interleave
open import Data.List
open import Data.Sum
open import label
open import RefWithoutSize
open import dataAuxFunction
open import renamingResult
open import TraceWithoutSize
open import addTick
open import process 
open import Size
open import choiceSetU
open import Data.Maybe
open import Data.Fin
open import Data.List
open import Data.Sum
open import renamingResult
open import TraceWithoutSize
open import RefWithoutSize
open import dataAuxFunction
open import externalChoice
open import addTick
open import internalChoice




swap⊎ : {c₀ c₁ : Choice} → ChoiceSet (c₀ ⊎' c₁) → ChoiceSet (c₁ ⊎' c₀)
swap⊎ (inj₁ x) = inj₂ x
swap⊎ (inj₂ y) = inj₁ y

Ass⊎ :  {c₀ c₁ c₂ : Choice} → ChoiceSet ((c₀ ⊎' c₁) ⊎' c₂) → ChoiceSet (c₀ ⊎' (c₁ ⊎' c₂)) 
Ass⊎ (inj₁ (inj₁ x)) = inj₁ x
Ass⊎ (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
Ass⊎ (inj₂ x) = inj₂ (inj₂ x)

Ass⊎ᵣ :  {c₀ c₁ c₂ : Choice} → ChoiceSet (c₀ ⊎' ( c₁ ⊎' c₂)) → ChoiceSet ((c₀ ⊎' c₁) ⊎' c₂) 
Ass⊎ᵣ (inj₁ x) = inj₁ (inj₁ x)
Ass⊎ᵣ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
Ass⊎ᵣ (inj₂ (inj₂ x)) = inj₂ x 





swap× : {c₀ c₁ : Choice} → ChoiceSet (c₀ ×' c₁) → ChoiceSet (c₁ ×' c₀)
swap× (x₀ ,, x₁) = (x₁ ,, x₀)

Ass× : {c₀ c₁ c₂ : Choice} → ChoiceSet (c₀ ×' (c₁ ×' c₂))  → ChoiceSet ((c₀ ×' c₁) ×' c₂) 
Ass× (x ,, (x₁ ,, x₂)) = ((x ,, x₁) ,, x₂)

Ass×' : {c₀ c₁ c₂ : Choice} → ChoiceSet ((c₀ ×' c₁) ×' c₂)  → ChoiceSet (c₀ ×' (c₁ ×' c₂)) 
Ass×' ((x ,, x₁) ,, x₂) = x ,, (x₁ ,, x₂) 


mutual
  Fmap+ : {c₀ c₁ c₂ c₃ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂)
             → (h :  ChoiceSet c₂ → ChoiceSet c₃)
             → (P :  Process+ ∞ c₀)
             → (fmap+ ((h ∘ (g ∘ f))) P) ⊑+ (fmap+ h (fmap+ g (fmap+ f P)))
  Fmap+ f g h P .[] .nothing empty = empty
  Fmap+ f g h P .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (Fmap∞ f g h (PE P x) l m x₁)
  Fmap+ f g h P l m (intc .l .m x x₁) = intc l m x (Fmap∞ f g h (PI P x) l m x₁)
  Fmap+ f g h P .[] .(just (h (g (f (PT P x))))) (terc x) = terc x

  Fmap∞ : {c₀ c₁ c₂ c₃ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂)
             → (h :  ChoiceSet c₂ → ChoiceSet c₃)
             → (P :  Process∞ ∞ c₀)
             → (fmap∞ ((h ∘ (g ∘ f))) P) ⊑∞ (fmap∞ h (fmap∞ g (fmap∞ f P)))
  forcet (Fmap∞ f g h P l m x) = Fmap f g h (forcep P) l m (forcet x)


  Fmap : {c₀ c₁ c₂ c₃ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂)
             → (h :  ChoiceSet c₂ → ChoiceSet c₃)
             → (P :  Process ∞ c₀)
             → (fmap ((h ∘ (g ∘ f))) P) ⊑ (fmap h (fmap g (fmap f P)))
  Fmap f g h (terminate x) l m x₁ = x₁
  Fmap f g h (node x) l m x₁ = tnode (Fmap+ f g h x l m (forcet' l m x₁))



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


  lemFmap∞R : {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
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
  addTimeFmapLemma+ : {c₀ c₁ c₂ : Choice} 
                     (f : ChoiceSet c₀ → ChoiceSet c₁) 
                     (g : ChoiceSet c₁ → ChoiceSet c₂) 
                     (P : Process+ ∞ c₀)
                     (a : ChoiceSet c₁)
                     → addTimed✓+ (g a) (fmap+ (g ∘ f) P) ⊑+ fmap+ g (addTimed✓+ a (fmap+ f P))
  addTimeFmapLemma+  {c₀} {c₁} {c₂} f g P a .[] .nothing empty = empty
  addTimeFmapLemma+  {c₀} {c₁} {c₂} f g P a .(Lab P x ∷ l) m (extc l .m x q) = extc l m x (lemFmap∞ f g (PE P x) l m q)
  addTimeFmapLemma+  {c₀} {c₁} {c₂} f g P a l m (intc .l .m x q) = intc l m x (addTimeFmapLemma∞ f g (PI P x) a l m q)
  addTimeFmapLemma+  {c₀} {c₁} {c₂} f g P a .[] .(just (g a)) (terc (inj₁ x)) = terc (inj₁ x)
  addTimeFmapLemma+  {c₀} {c₁} {c₂} f g P a .[] .(just (g (f (PT P y)))) (terc (inj₂ y)) = terc (inj₂ y) 


  addTimeFmapLemma∞ : {c₀ c₁ c₂ : Choice} 
                     (f : ChoiceSet c₀ → ChoiceSet c₁) 
                     (g : ChoiceSet c₁ → ChoiceSet c₂) 
                     (P : Process∞  ∞ c₀)
                     (a : ChoiceSet c₁)
                     → addTimed✓∞ (g a) (fmap∞ (g ∘ f) P) ⊑∞ fmap∞ g (addTimed✓∞ a (fmap∞ f P))
  forcet (addTimeFmapLemma∞  {c₀} {c₁} {c₂} f g P a l m q) = addTimeFmapLemma f g (forcep P) a l m (forcet q)


  addTimeFmapLemma : {c₀ c₁ c₂ : Choice} 
                     (f : ChoiceSet c₀ → ChoiceSet c₁) 
                     (g : ChoiceSet c₁ → ChoiceSet c₂) 
                     (P : Process ∞ c₀)
                     (a : ChoiceSet c₁)
                     → addTimed✓ (g a) (fmap (g ∘ f) P) ⊑ fmap g (addTimed✓ a (fmap f P))
  addTimeFmapLemma {c₀} {c₁} {c₂} f g (terminate x) a .[] .nothing (tnode empty) = tnode empty
  addTimeFmapLemma {c₀} {c₁} {c₂} f g (terminate x) a .(efq _ ∷ l) m (tnode (extc l .m () x₂))
  addTimeFmapLemma {c₀} {c₁} {c₂} f g (terminate x) a l m (tnode (intc .l .m () x₂))
  addTimeFmapLemma {c₀} {c₁} {c₂} f g (terminate x) a .[] .(just (g a)) (tnode (terc zero)) = tnode (terc zero)
  addTimeFmapLemma {c₀} {c₁} {c₂} f g (terminate x) a .[] .(just (g (f x))) (tnode (terc (suc zero))) =  (tnode (terc (suc zero)))
  addTimeFmapLemma {c₀} {c₁} {c₂} f g (terminate x) a .[] .(just (g (unifyA⊎A (if suc (suc _) then inj₁ a else (inj₂ (f x)))))) (tnode (terc (suc (suc ()))))
  addTimeFmapLemma {c₀} {c₁} {c₂} f g (node P) a l m (tnode q) = tnode (addTimeFmapLemma+ f g P a l m q)




mutual
  addTimeFmapLemma+R : {c₀ c₁ c₂ : Choice} 
                     (f : ChoiceSet c₀ → ChoiceSet c₁) 
                     (g : ChoiceSet c₁ → ChoiceSet c₂) 
                     (P : Process+ ∞ c₀)
                     (a : ChoiceSet c₁)
                     →  fmap+ g (addTimed✓+ a (fmap+ f P)) ⊑+  addTimed✓+ (g a) (fmap+ (g ∘ f) P)
  addTimeFmapLemma+R  {c₀} {c₁} {c₂} f g P a .[] .nothing empty = empty
  addTimeFmapLemma+R  {c₀} {c₁} {c₂} f g P a .(Lab P x ∷ l) m (extc l .m x q) = extc l m x (lemFmap∞R f g (PE P x) l m q)
  addTimeFmapLemma+R  {c₀} {c₁} {c₂} f g P a l m (intc .l .m x q) = intc l m x (addTimeFmapLemma∞R f g (PI P x) a l m q)
  addTimeFmapLemma+R  {c₀} {c₁} {c₂} f g P a .[] .(just (g a)) (terc (inj₁ x)) = terc (inj₁ x)
  addTimeFmapLemma+R  {c₀} {c₁} {c₂} f g P a .[] .(just (g (f (PT P y)))) (terc (inj₂ y)) = terc (inj₂ y) 


  addTimeFmapLemma∞R : {c₀ c₁ c₂ : Choice} 
                     (f : ChoiceSet c₀ → ChoiceSet c₁) 
                     (g : ChoiceSet c₁ → ChoiceSet c₂) 
                     (P : Process∞  ∞ c₀)
                     (a : ChoiceSet c₁)
                     →  fmap∞ g (addTimed✓∞ a (fmap∞ f P)) ⊑∞  addTimed✓∞ (g a) (fmap∞ (g ∘ f) P)
  forcet (addTimeFmapLemma∞R  {c₀} {c₁} {c₂} f g P a l m q) = addTimeFmapLemmaR f g (forcep P) a l m (forcet q)


  addTimeFmapLemmaR : {c₀ c₁ c₂ : Choice} 
                     (f : ChoiceSet c₀ → ChoiceSet c₁) 
                     (g : ChoiceSet c₁ → ChoiceSet c₂) 
                     (P : Process ∞ c₀)
                     (a : ChoiceSet c₁)
                     →  fmap g (addTimed✓ a (fmap f P)) ⊑  addTimed✓ (g a) (fmap (g ∘ f) P)
  addTimeFmapLemmaR {c₀} {c₁} {c₂} f g (terminate x) a .[] .nothing (tnode empty) = (tnode empty)
  addTimeFmapLemmaR {c₀} {c₁} {c₂} f g (terminate x) a .(efq _ ∷ l) m (tnode (extc l .m () x₂))
  addTimeFmapLemmaR {c₀} {c₁} {c₂} f g (terminate x) a l m (tnode (intc .l .m () x₂))
  addTimeFmapLemmaR {c₀} {c₁} {c₂} f g (terminate x) a .[] .(just (g a)) (tnode (terc zero)) = (tnode (terc zero))
  addTimeFmapLemmaR {c₀} {c₁} {c₂} f g (terminate x) a .[] .(just (g (f x))) (tnode (terc (suc zero))) = (tnode (terc (suc zero)))
  addTimeFmapLemmaR {c₀} {c₁} {c₂} f g (terminate x) a .[] .(just (unifyA⊎A (if suc (suc _) then inj₁ (g a) else (inj₂ (g (f x)))))) (tnode (terc (suc (suc ()))))
  addTimeFmapLemmaR {c₀} {c₁} {c₂} f g (node x) a l m (tnode x₁) = tnode (addTimeFmapLemma+R f g x a l m x₁)

