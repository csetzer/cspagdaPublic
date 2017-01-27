module renamingResult where

open import process
open ∞Process
open import Size

mutual 
  fmap : (i : Size) → {A B : Set} → (A → B) → ∞Process i A → ∞Process i B
  force (fmap i f x )  j = fmap' j f (force x j)

  fmap' :  (i : Size) → {A B : Set} → (A → B) → Process i A → Process i B  
  fmap' i f (node E Lab PE I PI Stat) = node E Lab (λ x → fmap i f (PE x)) I (λ x → fmap i f (PI x)) Stat
  fmap' i f (terminate x) = terminate (f x)

