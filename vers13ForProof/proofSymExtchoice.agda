module proofSymExtchoice where 
open import process 
open import indTr
open Process'
open Process
open Process∞
open Tr∞
open import Size
open import choiceSetU
open import auxData
open import Data.Maybe 
open import interleave
open import Data.List
open import Data.Sum
open import label
open import renamingResult
open import extchoice
open import auxData
open import dataAuxFunction

swap⊎ : {c₀ c₁ : Choice} → ChoiceSet (c₀ ⊎' c₁) → ChoiceSet (c₁ ⊎' c₀)
swap⊎ (inj₁ x) = inj₂ x
swap⊎ (inj₂ y) = inj₁ y


-- to be shown
-- fmaplem : Tr∞ l m (fmap∞ f (fmap∞ g P)) → Tr∞ l m (fmap∞ (f ∘ g) P)    --------------> Tr l m (fmap (λ a → f (g a)) p)
-- fmaplem : Tr∞ l m (fmap∞ (f ∘ g) P) → Tr∞ l m (fmap∞ f (fmap∞ g P)) 

-- and then you get from  
-- Tr∞ l m (fmap∞ inj₁ (PE P x)) 
-- Tr∞ l m (fmap∞ swap⊎ (fmap∞ inj₂ (PE P x)))
-- because
-- swap⊎  ∘ inj₂ = inj₁





mutual
  lemFmap : {i : Size} → {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process i c₀)
             → (fmap (g ∘ f) P) ⊑ (fmap g (fmap f P))
  lemFmap f g P .[] .nothing empty = empty
  lemFmap f g P .(Lab P x ∷ l) m (extchoice l .m x x₁) = extchoice l m x (lemFmap∞ f g (PE P x) l m x₁)
  lemFmap f g P l m (intchoice .l .m x x₁) = intchoice l m x (lemFmap∞ f g (PI P x) l m x₁)
  lemFmap f g P .[] .(just (g (f (PT P x)))) (terchoice x) = (terchoice x)

  
  lemFmap∞ : {i : Size} → {c₀ c₁ c₂ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁)
             → (g : ChoiceSet c₁ → ChoiceSet c₂) 
             → (P :  Process∞  i c₀)
             → (fmap∞ (g ∘ f) P) ⊑∞  (fmap∞ g (fmap∞ f P))
  forcet (lemFmap∞ f g P l m x) = lemFmap f g (forcep P) l m (forcet x) 



mutual 
 Sym□ : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process i c₀)
         → (Q : Process i c₁)
         → Ref (P □ Q) (fmap swap⊎ (Q □ P))
 Sym□ P Q .[] .nothing empty = empty
 Sym□ P Q .(Lab P x ∷ l) m (extchoice l .m (inj₁ x) x₁) = extchoice l m (inj₂ x) (lemFmap∞ inj₂ swap⊎ (PE P x) l m x₁)
 Sym□ P Q .(Lab Q y ∷ l) m (extchoice l .m (inj₂ y) x₁) = extchoice l m (inj₁ y) (lemFmap∞ inj₁ swap⊎ (PE Q y) l m x₁)
 Sym□ P Q l m (intchoice .l .m (inj₁ x) x₁) = intchoice l m (inj₂ x) (Sym□∞p (PI P x) Q l m x₁)
 Sym□ P Q l m (intchoice .l .m (inj₂ y) x₁) = intchoice l m (inj₁ y) (Sym□p∞ P (PI Q y) l m x₁)
 Sym□ P Q .[] .(just (inj₁ (PT P x))) (terchoice (inj₁ x)) = terchoice (inj₂ x)
 Sym□ P Q .[] .(just (inj₂ (PT Q y))) (terchoice (inj₂ y)) = terchoice (inj₁ y)




 Sym□p∞  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process  i c₀)
         → (Q : Process∞ i c₁)
         → Ref∞ {i} {c₀ ⊎' c₁} (P □p∞ Q) (fmap∞ {c₁ ⊎' c₀} {c₀ ⊎' c₁} swap⊎ {i} (Q □∞p P))
 forcet (Sym□p∞ {i} {c₀} {c₁} P Q l m x) = Sym□ P (forcep Q) l m (forcet x)

 Sym□∞p  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process∞ i c₀)
         → (Q : Process  i c₁)
         → Ref∞ {i}  (P □∞p Q) (fmap∞  swap⊎ {i} (Q □p∞ P))
 forcet (Sym□∞p P Q l m x)  = Sym□ (forcep P) Q l m (forcet x)





{-
swap⊎' : {c₀ c₁ c₂ : Choice} → ChoiceSet ((c₀ ⊎' c₁) ⊎' c₂) → ChoiceSet (c₀ ⊎' (c₁ ⊎' c₂))
swap⊎' (inj₁ (inj₁ x)) = inj₁ x
swap⊎' (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
swap⊎' (inj₂ y) = inj₂ (inj₂ y)


swap⊎'' : {c₀ c₁ c₂ : Choice} → ChoiceSet  (c₀ ⊎' (c₁ ⊎' c₂)) → ChoiceSet ((c₀ ⊎' c₁) ⊎' c₂)
swap⊎'' (inj₁ x) = inj₁ (inj₁ x)
swap⊎'' (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
swap⊎'' (inj₂ (inj₂ y)) = inj₂ y


mutual 
  Tr□ : {i : Size} → {j : Size< i} → {c₀ c₁ c₂ : Choice}
         → (P : Process i c₀)
         → (Q : Process i c₁)
         → (Z : Process i c₂)
         → Ref {i} (P □ (Q □ Z)) (fmap swap⊎' (((P □ Q) □ Z)))
  Tr□ P Q Z .[] .nothing empty = empty
  Tr□ P Q Z .(Lab P x ∷ l) m (extchoice l .m (inj₁ x) x₁) = extchoice l m ((inj₁ (inj₁ x))) {!Tr□p∞'!}
  Tr□ P Q Z .(Lab Q x ∷ l) m (extchoice l .m (inj₂ (inj₁ x)) x₁) = extchoice l m ((inj₁ (inj₂ x))) {!Tr□p∞'!}
  Tr□ P Q Z .(Lab Z y ∷ l) m (extchoice l .m (inj₂ (inj₂ y)) x₁) = extchoice l m ((inj₂ y)) {!Tr□p∞'!}
  Tr□ {i} P Q Z l m (intchoice .l .m (inj₁ x) x₁) = intchoice l m (inj₁ (inj₁ x)) {!!} --(Tr□p∞'  (PI P x) Q Z l m x₁)
  Tr□ P Q Z l m (intchoice .l .m (inj₂ (inj₁ x)) x₁) = intchoice l m (inj₁ (inj₂ x)) {!Tr□p∞'!}
  Tr□ P Q Z l m (intchoice .l .m (inj₂ (inj₂ y)) x₁) = intchoice l m (inj₂ y) {!Tr□p∞'!}
  Tr□ P Q Z .[] .(just (inj₁ (PT P x))) (terchoice (inj₁ x)) = terchoice (inj₁ (inj₁ x))
  Tr□ P Q Z .[] .(just (inj₂ (inj₁ (PT Q x)))) (terchoice (inj₂ (inj₁ x))) = terchoice (inj₁ (inj₂ x))
  Tr□ P Q Z .[] .(just (inj₂ (inj₂ (PT Z y)))) (terchoice (inj₂ (inj₂ y))) = terchoice (inj₂ y)
-}
