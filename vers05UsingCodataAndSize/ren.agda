{-# OPTIONS --copatterns #-}

module ren  where
open import process 
open import Size
open import pro 
open ∞Process
open ∞Processx

------------- Renaming ---------------------


mutual 
   Rename :  (i : Size) → {A : Set} → (f : Label → Label) → ∞Process i A  → ∞Process i A
   force (Rename i f a) j = Rename' j f (force a j)
   
   Rename' : (i : Size) → {A : Set} → (f : Label → Label) → Process i A  → Process i A
   Rename' i f (node E Lab PE I PI) = node E (f ∘ Lab) (λ x → PE x ) I (λ x → PI x)
   Rename' i f (terminate x) = terminate x

rename : {i : Size} → {A : Set} → (f : Label → Label) → ∞Process i A  → ∞Process i A
rename = Rename _

rename' : {i : Size} → {A : Set} → (f : Label → Label) → Process i A  → Process i A
rename' = Rename' _


