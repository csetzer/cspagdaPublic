module proofSymInterleaving where 

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

swap⊎ : {c₀ c₁ : Choice} → ChoiceSet (c₀ ⊎' c₁) → ChoiceSet (c₁ ⊎' c₀)
swap⊎ (inj₁ x) = inj₂ x
swap⊎ (inj₂ y) = inj₁ y

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
 S|||+ :  {i : Size} {c₀ c₁ : Choice} (P : Process+ i c₀) (Q : Process+ i c₁)
        →  (P |||++ Q) ⊑+ (fmap+ swap× (Q |||++ P))
 S|||+ P Q .[] .nothing empty = empty
 S|||+ P Q .(Lab Q x ∷ l) m (extc l .m (inj₁ x) q)  = extc l m (inj₂ x)  (S|||+∞  P (PE Q x) l m q) 
 S|||+ P Q .(Lab P x ∷ l) m (extc l .m (inj₂ x) q)  = extc l m (inj₁ x)  (S|||∞+  (PE P x) Q l m q)
 S|||+ P Q l m (intc .l .m (inj₁ x) q)              = intc l m (inj₂ x)  (S|||+∞  P (PI Q x) l m q)
 S|||+ P Q l m (intc .l .m (inj₂ x) q)              = intc l m (inj₁ x)  (S|||∞+  (PI P x) Q l m q)
 S|||+ P Q .[] .(just (PT P x ,, PT Q y)) (terc (y ,, x)) = terc (x ,, y)

 S||| : {i : Size} → {c₀ c₁ : Choice} → (P : Process i c₀) → (Q : Process i c₁)
         →  (P ||| Q) ⊑ (fmap swap× (Q ||| P))
 S||| (terminate x) (terminate x') l m q = q
 S||| (terminate x) (node P) l m (tnode q) = tnode (lemFmap+  (λ a → a ,, x) swap×  P l m q  )
 S||| (node P) (terminate x) l m (tnode q) = tnode (lemFmap+ (_,,_ x) swap×  P l m q )
 S||| (node P) (node Q) l m (tnode q) = tnode (S|||+ P Q l m q)

 S|||+p  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process+ i c₀)
         → (Q : Process  i c₁)
         → Ref+ {i}  (P |||+p Q) (fmap+  swap× {i} (Q |||p+ P))
 S|||+p P (terminate x) l m q = lemFmap+ (_,,_ x) swap×  P l m q 
 S|||+p P (node Q) l m q = S|||+ P Q l m q


 S|||p+  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process i c₀)
         → (Q : Process+  i c₁)
         → Ref+ {i}  (P |||p+ Q) (fmap+  swap× {i} (Q |||+p P))
 S|||p+ (terminate x) Q l m q = lemFmap+ (λ a → a ,, x) swap×  Q l m q 
 S|||p+ (node P) Q l m q = S|||+ P Q l m q

 S|||+∞  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process+ i c₀)
         → (Q : Process∞  i c₁)
         → Ref∞ {i}  (P |||+∞ Q) (fmap∞  swap× {i} (Q |||∞+ P))
 forcet (S|||+∞ P Q l m x) = tnode (S|||+p P (forcep Q) l m (forcet' l m (forcet x)))  


 S|||∞+  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process∞  i c₀)
         → (Q : Process+  i c₁)
         → Ref∞ {i}  (P |||∞+ Q) (fmap∞  swap× {i} (Q |||+∞ P))
 forcet (S|||∞+ P Q l m x) = tnode (S|||p+ (forcep P) Q l m (forcet' l m (forcet x)))  





mutual
  lemFmap+R : {i : Size} → {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process+ i c₀)
             → (fmap+ g (fmap+ f P)) ⊑+ (fmap+ (g ∘ f) P)
  lemFmap+R f g P .[] .nothing empty = empty
  lemFmap+R f g P .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (lemFmap∞R f g (PE P x) l m x₁) 
  lemFmap+R f g P l m (intc .l .m x x₁) = intc l m x (lemFmap∞R f g (PI P x) l m x₁) 
  lemFmap+R f g P .[] .(just (g (f (PT P x)))) (terc x) = terc x


  lemFmap∞R : {i : Size} → {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process∞  i c₀)
             → (fmap∞ g (fmap∞ f P)) ⊑∞  (fmap∞ (g ∘ f) P)
  forcet (lemFmap∞R f g P l m x) = lemFmapR f g (forcep P) l m (forcet x) 


  lemFmapR : {i : Size} → {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process  i c₀)
             → (fmap g (fmap f P)) ⊑  (fmap (g ∘ f) P)
  lemFmapR f g (terminate x) l m x₁ = x₁
  lemFmapR f g (node P) l m (tnode x) = tnode (lemFmap+R f g P l m x)



mutual 

 S|||+R : {i : Size} → {c₀ c₁ : Choice} → (P : Process+ i c₀) → (Q : Process+ i c₁)
         →  (fmap+ swap× (Q |||++ P)) ⊑+ (P |||++ Q)
 S|||+R P Q .[] .nothing empty = empty
 S|||+R P Q .(Lab P x ∷ l) m (extc l .m (inj₁ x) x₁) = extc l m (inj₂ x) (S|||∞+R (PE P x) Q l m x₁)
 S|||+R P Q .(Lab Q y ∷ l) m (extc l .m (inj₂ y) x₁) = extc l m (inj₁ y) (S|||+∞R P (PE Q y) l m x₁) 
 S|||+R P Q l m (intc .l .m (inj₁ x) x₁)             = intc l m (inj₂ x) (S|||∞+R (PI P x) Q l m x₁)
 S|||+R P Q l m (intc .l .m (inj₂ y) x₁)             = intc l m (inj₁ y) (S|||+∞R P (PI Q y) l m x₁)
 S|||+R P Q .[] .(just (PT P x ,, PT Q x₁)) (terc (x ,, x₁)) = terc (x₁ ,, x)


 S|||R : {i : Size} → {c₀ c₁ : Choice} → (P : Process i c₀) → (Q : Process i c₁)
         → (fmap swap× (Q ||| P))  ⊑ (P ||| Q)
 S|||R (terminate x) (terminate x') l m q = q
 S|||R (terminate x) (node P) l m (tnode q) = tnode (lemFmap+R  (λ a → a ,, x) swap×  P l m q  )
 S|||R (node P) (terminate x) l m (tnode q) = tnode (lemFmap+R (_,,_ x) swap×  P l m q )
 S|||R (node P) (node Q) l m (tnode q) = tnode (S|||+R P Q l m q)


 S|||+pR  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process+ i c₀)
         → (Q : Process  i c₁)
         → Ref+ {i}  (fmap+  swap× {i} (Q |||p+ P)) (P |||+p Q)
 S|||+pR P (terminate x) l m q = lemFmap+R (_,,_ x) swap×  P l m q 
 S|||+pR P (node Q) l m q = S|||+R P Q l m q


 S|||p+R  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process i c₀)
         → (Q : Process+  i c₁)
         → Ref+ {i}  (fmap+  swap× {i} (Q |||+p P)) (P |||p+ Q) 
 S|||p+R (terminate x) Q l m q = lemFmap+R (λ a → a ,, x) swap×  Q l m q 
 S|||p+R (node P) Q l m q = S|||+R P Q l m q

 S|||+∞R  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process+ i c₀)
         → (Q : Process∞  i c₁)
         → Ref∞ {i}  (fmap∞  swap× {i} (Q |||∞+ P)) (P |||+∞ Q)
 forcet (S|||+∞R P Q l m x) = tnode (S|||+pR P (forcep Q) l m (forcet' l m (forcet x)))  


 S|||∞+R  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process∞  i c₀)
         → (Q : Process+  i c₁)
         → Ref∞ {i}  (fmap∞  swap× {i} (Q |||+∞ P)) (P |||∞+ Q) 
 forcet (S|||∞+R P Q l m x) = tnode (S|||p+R (forcep P) Q l m (forcet' l m (forcet x)))  































