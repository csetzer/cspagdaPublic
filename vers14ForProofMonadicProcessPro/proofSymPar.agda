module proofSymPar where 

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
open import parallelSimple

swap× : {c₀ c₁ : Choice} → ChoiceSet (c₀ ×' c₁) → ChoiceSet (c₁ ×' c₀)
swap× (x₀ ,, x₁) = (x₁ ,, x₀)

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
 S[]+ :  {i : Size} {c₀ c₁ : Choice} (P : Process+ i c₀) (A  B : Label → Bool) (Q : Process+ i c₁)
        → (P [ A ]||+[ B ] Q) ⊑+ fmap+ swap× ((Q [ B ]||+[ A ] P))

 S[]+ P A B Q .[] .nothing empty = empty
 S[]+ P A B Q .(Lab Q a ∷ l) m (extc l .m (inj₁ (sub a x)) x₁) = extc l m (inj₂ (inj₁ ( sub a x))) (S[]+∞ P A B (PE Q a) l m x₁)
 S[]+ P A B Q .(Lab P a ∷ l) m (extc l .m (inj₂ (inj₁ (sub a x))) x₁) =  extc l m (inj₁ (sub a x)) (S[]∞+ (PE P a) A B Q l m x₁)
 S[]+  {i} {c₀} {c₁} P A B Q .(Lab Q x ∷ l) m (extc l .m (inj₂ (inj₂ (sub (x ,, x₁) x₂))) x₃) =  {!m!}
 S[]+ P A B Q l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₂ x) (S[]+∞ P A B (PI Q x) l m x₁)
 S[]+ P A B Q l m (intc .l .m (inj₂ y) x₁) = intc l m (inj₁ y) (S[]∞+ (PI P y) A B Q l m x₁)
 S[]+ P A B Q .[] .(just (PT P x₁ ,, PT Q x)) (terc (x ,, x₁)) = terc ((x₁ ,, x))

--extc l m ((inj₂ (inj₂ (sub {!(x₁ ,, x)!} x₂)))) {!!}
--extc l m  (inj₂ (inj₂ (sub (x₁ ,, x) {!!}))) {!!}

 S[]+∞  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process+ i c₀)
         → (A  B : Label → Bool)
         → (Q : Process∞  i c₁)
         → Ref∞ {i} (P [ A ]||+∞[ B ] Q) (fmap∞ swap× ((Q [ B ]||∞+[ A ] P))) 
 forcet (S[]+∞ P A B Q l m x) = tnode (S[]+p P A B (forcep Q) l m (forcet' l m (forcet x)))


 S[]∞+  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process∞  i c₀)
         → (A  B : Label → Bool)
         → (Q : Process+  i c₁)
         → Ref∞ {i} (P [ A ]||∞+[ B ] Q) (fmap∞ swap× ((Q [ B ]||+∞[ A ] P)))
 forcet (S[]∞+ P  A B Q l m x) = tnode (S[]p+ (forcep P) A B Q l m ((forcet' l m (forcet x))))



 S[]+p  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process+ i c₀)
         → (A  B : Label → Bool)
         → (Q : Process  i c₁)
         → Ref+ {i} (P [ A ]||+p[ B ] Q) (fmap+ swap× ((Q [ B ]||p+[ A ] P)))
 S[]+p P A B (terminate x) l m q = lemFmap+ (_,,_ x) swap× (P ↾+ (A ∖ B)) l m q
 S[]+p P A B (node Q) l m q = S[]+ P A B Q l m q


 S[]p+  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process i c₀)
         → (A  B : Label → Bool)         
         → (Q : Process+  i c₁)
         → Ref+ {i} (P [ A ]||p+[ B ] Q) (fmap+ swap× ((Q [ B ]||+p[ A ] P)))
 S[]p+ (terminate x) Q l m q = lemFmap+ (λ a → a ,, x) swap× (m ↾+ (l ∖ Q)) q
 S[]p+ (node P) Q l m q = S[]+ P Q l m q











{-

mutual 
 S[]R+ :  {i : Size} {c₀ c₁ : Choice} (P : Process+ i c₀) (A  B : Label → Bool) (Q : Process+ i c₁)
        →  (fmap+ swap×(Q [ B ]||+[ A ] P)) ⊑+  (P [ A ]||+[ B ] Q)
 S[]R+ P A B Q .[] .nothing empty = empty
 S[]R+ P A B Q .(Lab P a ∷ l) m (extc l .m (inj₁ (sub a x)) x₁) = extc l m {!!} {!!}
 S[]R+ P A B Q .(Lab Q a ∷ l) m (extc l .m (inj₂ (inj₁ (sub a x))) x₁) = {!!}
 S[]R+ P A B Q .(Lab (P [ A ]||+[ B ] Q) (inj₂ (inj₂ (sub a x))) ∷ l) m (extc l .m (inj₂ (inj₂ (sub a x))) x₁) = {!!}
 S[]R+ P A B Q l m (intc .l .m x x₁) = {!!}
 S[]R+ P A B Q .[] .(just (PT (P [ A ]||+[ B ] Q) x)) (terc x) = {!!}
-}
