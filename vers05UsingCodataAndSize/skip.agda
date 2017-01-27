{-# OPTIONS --copatterns #-}

module skip where
open import process 
open import Size
open import pro
open ∞Process
open ∞Processx

----------------- SKIP Operation -------------------


SKIP : (i : Size) → {A : Set} →  A →  ∞Process i A
force (SKIP  i a) j = node ∅' efq efq ⊤' (λ _ → delay i (terminate a))
 

Skip :  {i : Size} → {A : Set} → A → (∞Process i A)
Skip = SKIP _



SKIP' : (i : Size) → {A : Set} →  A →  ∞Processx i A
forcex (SKIP'  i a) j = node (thenode ∅' efq efq ⊤' (λ _ → delayx i (terminate a)))
 

Skip' :  {i : Size} → {A : Set} → A → (∞Processx i A)
Skip' = SKIP' _


