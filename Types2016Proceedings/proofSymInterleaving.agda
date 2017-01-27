module proofSymInterleaving where 


open import process 
open import Size
open import choiceSetU
open import Data.Maybe
open import Data.List
open import Data.Sum
open import renamingResult
open import TraceWithoutSize
open import RefWithoutSize
open import lemFmap
open import auxData
open import Data.Product
open import interleave
open import traceEquivalence
open import Data.Product

mutual 
 S|||+ : {c₀ c₁ : Choice} (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁)
        →  (P |||++ Q) ⊑+ (fmap+ swap× (Q |||++ P))
 S|||+ P Q .[] .nothing empty = empty
 S|||+ P Q .(Lab Q x ∷ l) m (extc l .m (inj₁ x) q)  = extc l m (inj₂ x)  (S|||+∞  P (PE Q x) l m q) 
 S|||+ P Q .(Lab P x ∷ l) m (extc l .m (inj₂ x) q)  = extc l m (inj₁ x)  (S|||∞+  (PE P x) Q l m q)
 S|||+ P Q l m (intc .l .m (inj₁ x) q)              = intc l m (inj₂ x)  (S|||+∞  P (PI Q x) l m q)
 S|||+ P Q l m (intc .l .m (inj₂ x) q)              = intc l m (inj₁ x)  (S|||∞+  (PI P x) Q l m q)
 S|||+ P Q .[] .(just (PT P x ,, PT Q y)) (terc (y ,, x)) = terc (x ,, y)

 S||| :  {c₀ c₁ : Choice} → (P : Process ∞ c₀) → (Q : Process ∞ c₁)
         →  (P ||| Q) ⊑ (fmap swap× (Q ||| P))
 S||| (terminate x) (terminate x') l m q = q
 S||| (terminate x) (node P) l m (tnode q) = tnode (lemFmap+  (λ a → a ,, x) swap×  P l m q  )
 S||| (node P) (terminate x) l m (tnode q) = tnode (lemFmap+ (_,,_ x) swap×  P l m q )
 S||| (node P) (node Q) l m (tnode q) = tnode (S|||+ P Q l m q)

 S|||+p  : {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (Q : Process  ∞ c₁)
         → Ref+   (P |||+p Q) (fmap+  swap×  (Q |||p+ P))
 S|||+p P (terminate x) l m q = lemFmap+ (_,,_ x) swap×  P l m q 
 S|||+p P (node Q) l m q = S|||+ P Q l m q


 S|||p+  : {c₀ c₁ : Choice}
         → (P : Process ∞ c₀)
         → (Q : Process+ ∞ c₁)
         → Ref+ (P |||p+ Q) (fmap+  swap× (Q |||+p P))
 S|||p+ (terminate x) Q l m q = lemFmap+ (λ a → a ,, x) swap×  Q l m q 
 S|||p+ (node P) Q l m q = S|||+ P Q l m q

 S|||+∞  : {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (Q : Process∞  ∞ c₁)
         → Ref∞ (P |||+∞ Q) (fmap∞  swap× (Q |||∞+ P))
 forcet (S|||+∞ P Q l m x) = tnode (S|||+p P (forcep Q) l m (forcet' l m (forcet x)))  


 S|||∞+  : {c₀ c₁ : Choice}
         → (P : Process∞  ∞ c₀)
         → (Q : Process+  ∞ c₁)
         → Ref∞ (P |||∞+ Q) (fmap∞  swap× (Q |||+∞ P))
 forcet (S|||∞+ P Q l m x) = tnode (S|||p+ (forcep P) Q l m (forcet' l m (forcet x)))  





mutual 
 S|||+R : {c₀ c₁ : Choice} → (P : Process+ ∞ c₀) → (Q : Process+ ∞ c₁)
         →  (fmap+ swap× (Q |||++ P)) ⊑+ (P |||++ Q)
 S|||+R P Q .[] .nothing empty = empty
 S|||+R P Q .(Lab P x ∷ l) m (extc l .m (inj₁ x) x₁) = extc l m (inj₂ x) (S|||∞+R (PE P x) Q l m x₁)
 S|||+R P Q .(Lab Q y ∷ l) m (extc l .m (inj₂ y) x₁) = extc l m (inj₁ y) (S|||+∞R P (PE Q y) l m x₁) 
 S|||+R P Q l m (intc .l .m (inj₁ x) x₁)             = intc l m (inj₂ x) (S|||∞+R (PI P x) Q l m x₁)
 S|||+R P Q l m (intc .l .m (inj₂ y) x₁)             = intc l m (inj₁ y) (S|||+∞R P (PI Q y) l m x₁)
 S|||+R P Q .[] .(just (PT P x ,, PT Q x₁)) (terc (x ,, x₁)) = terc (x₁ ,, x)


 S|||R : {c₀ c₁ : Choice} → (P : Process ∞ c₀) → (Q : Process ∞ c₁)
         → (fmap swap× (Q ||| P))  ⊑ (P ||| Q)
 S|||R (terminate x) (terminate x') l m q = q
 S|||R (terminate x) (node P) l m (tnode q) = tnode (lemFmap+R  (λ a → a ,, x) swap×  P l m q  )
 S|||R (node P) (terminate x) l m (tnode q) = tnode (lemFmap+R (_,,_ x) swap×  P l m q )
 S|||R (node P) (node Q) l m (tnode q) = tnode (S|||+R P Q l m q)


 S|||+pR  : {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (Q : Process  ∞ c₁)
         → Ref+ (fmap+  swap× (Q |||p+ P)) (P |||+p Q)
 S|||+pR P (terminate x) l m q = lemFmap+R (_,,_ x) swap×  P l m q 
 S|||+pR P (node Q) l m q = S|||+R P Q l m q


 S|||p+R  : {c₀ c₁ : Choice}
         → (P : Process ∞ c₀)
         → (Q : Process+ ∞ c₁)
         → Ref+ (fmap+  swap×  (Q |||+p P)) (P |||p+ Q) 
 S|||p+R (terminate x) Q l m q = lemFmap+R (λ a → a ,, x) swap×  Q l m q 
 S|||p+R (node P) Q l m q = S|||+R P Q l m q

 S|||+∞R  : {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (Q : Process∞ ∞ c₁)
         → Ref∞  (fmap∞  swap× (Q |||∞+ P)) (P |||+∞ Q)
 forcet (S|||+∞R P Q l m x) = tnode (S|||+pR P (forcep Q) l m (forcet' l m (forcet x)))  


 S|||∞+R  : {c₀ c₁ : Choice}
         → (P : Process∞  ∞ c₀)
         → (Q : Process+  ∞ c₁)
         → Ref∞ (fmap∞  swap× (Q |||+∞ P)) (P |||∞+ Q) 
 forcet (S|||∞+R P Q l m x) = tnode (S|||p+R (forcep P) Q l m (forcet' l m (forcet x)))  



 ≡S|||+ : {c₀ c₁ : Choice} (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁)
        →  (P |||++ Q) ≡+  (fmap+  swap× (Q |||++ P))
 ≡S|||+ P Q = (S|||+ P Q) , (S|||+R P Q)
