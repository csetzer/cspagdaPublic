module proofSymExt where 
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
open import lemFmap
open import traceEquivalence
open import Data.Product


mutual 
 S□+ : {c₀ c₁ : Choice} (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁)
        →  (P □++ Q) ⊑+ (fmap+ swap⊎ (Q □++ P))
 S□+ P Q .[] .nothing empty = empty
 S□+ P Q .(Lab Q x ∷ l) m (extc l .m (inj₁ x) x₁) = extc l m (inj₂ x) (lemFmap∞ inj₁ swap⊎ (PE Q x) l m x₁)
 S□+ P Q .(Lab P y ∷ l) m (extc l .m (inj₂ y) x₁) = extc l m (inj₁ y) (lemFmap∞ inj₂ swap⊎ (PE P y) l m x₁)
 S□+ P Q l m (intc .l .m (inj₁ x) x₁) =  intc l m (inj₂ x) (S□+∞ P (PI Q x) l m x₁)
 S□+ P Q l m (intc .l .m (inj₂ y) x₁) =  intc l m (inj₁ y) (S□∞+ (PI P y) Q l m x₁)
 S□+ P Q .[] .(just (inj₂ (PT Q x))) (terc (inj₁ x)) = terc (inj₂ x)
 S□+ P Q .[] .(just (inj₁ (PT P y))) (terc (inj₂ y)) = terc (inj₁ y)


 S□+∞  : {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (Q : Process∞ ∞ c₁)
         → Ref∞   (P □+∞+ Q) (fmap∞  swap⊎ (Q □∞++ P))
 forcet (S□+∞ P Q l m x) =  tnode (S□+p P (forcep Q) l m (forcet' l m (forcet x)))
 
 S□+p  : {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (Q : Process  ∞ c₁)
         → Ref+ (P □+p+ Q) (fmap+ swap⊎ (Q □p++ P))
 S□+p P (terminate x) l m q = addTimeFmapLemma+ inj₂ swap⊎ P (inj₁ x) l m q
 S□+p P (node Q) l m q =  S□+ P Q l m q


 S□∞+  : {c₀ c₁ : Choice}
         → (P : Process∞ ∞ c₀)
         → (Q : Process+ ∞ c₁)
         → Ref∞ (P □∞++ Q) (fmap∞  swap⊎ (Q □+∞+ P))
 forcet (S□∞+ P Q l m x) = tnode (S□p+ (forcep P)  Q l m (forcet' l m (forcet x)))


 S□p+  : {c₀ c₁ : Choice}
         → (P : Process ∞ c₀)
         → (Q : Process+ ∞ c₁)
         → Ref+ (P □p++ Q) (fmap+ swap⊎ (Q □+p+ P))
 S□p+ (terminate x) P l m q = addTimeFmapLemma+ inj₁ swap⊎ P (inj₂ x) l m q
 S□p+ (node Q) P l m q = S□+ Q P l m q




mutual 
 S□+R : {c₀ c₁ : Choice} (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁)
        →   (fmap+ swap⊎ (Q □++ P)) ⊑+ (P □++ Q)
 S□+R P Q .[] .nothing empty = empty
 S□+R P Q .(Lab P x ∷ l) m (extc l .m (inj₁ x) x₁) = extc l m (inj₂ x) (lemFmap∞R inj₂ swap⊎ (PE P x) l m x₁)
 S□+R P Q .(Lab Q y ∷ l) m (extc l .m (inj₂ y) x₁) = extc l m (inj₁ y) (lemFmap∞R inj₁ swap⊎ (PE Q y) l m x₁)
 S□+R P Q l m (intc .l .m (inj₁ x) x₁) =  intc l m (inj₂ x) (S□∞+R (PI P x) Q l m x₁)
 S□+R P Q l m (intc .l .m (inj₂ y) x₁) =  intc l m (inj₁ y) (S□+∞R P (PI Q y) l m x₁)
 S□+R P Q .[] .(just (inj₁ (PT P x))) (terc (inj₁ x)) = (terc (inj₂ x))
 S□+R P Q .[] .(just (inj₂ (PT Q y))) (terc (inj₂ y)) = (terc (inj₁ y))



 S□+∞R  : {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (Q : Process∞ ∞ c₁)
         → Ref∞  (fmap∞  swap⊎ (Q □∞++ P))   (P □+∞+ Q)
 forcet (S□+∞R P Q l m x) =  tnode (S□+pR P (forcep Q) l m (forcet' l m (forcet x)))
 
 S□+pR  : {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (Q : Process  ∞ c₁)
         → Ref+  (fmap+ swap⊎ (Q □p++ P)) (P □+p+ Q)
 S□+pR P (terminate x) l m q = addTimeFmapLemma+R inj₂ swap⊎ P (inj₁ x) l m q
 S□+pR P (node Q) l m q =  S□+R P Q l m q


 S□∞+R  : {c₀ c₁ : Choice}
         → (P : Process∞ ∞ c₀)
         → (Q : Process+ ∞ c₁)
         → Ref∞  (fmap∞  swap⊎ (Q □+∞+ P)) (P □∞++ Q)
 forcet (S□∞+R P Q l m x) =  tnode (S□p+R (forcep P)  Q l m (forcet' l m (forcet x)))


 S□p+R  : {c₀ c₁ : Choice}
         → (P : Process ∞ c₀)
         → (Q : Process+ ∞ c₁)
         → Ref+  (fmap+ swap⊎ (Q □+p+ P)) (P □p++ Q)
 S□p+R (terminate x) P l m q =   addTimeFmapLemma+R inj₁ swap⊎ P (inj₂ x) l m q
 S□p+R (node Q) P l m q = S□+R Q P l m q




 ≡□+ : {c₀ c₁ : Choice} (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁)
        → (P □++ Q) ≡+  (fmap+ swap⊎ (Q □++ P))
 ≡□+ P Q =  S□+ P Q , S□+R P Q

