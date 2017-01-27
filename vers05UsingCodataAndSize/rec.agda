{-# OPTIONS --copatterns #-}

module rec where
open import process 
open import Size
open import pro 
open ∞Process
open ∞Processx
open import seq

--------------------------- Rec ------------------------

_>>=+_ : {i : Size} → {A B : Set} → Process+ i A → (A → ∞Process i B) → Process i B
_>>=+_ {i} (node E Lab PE I PI)  q = node E Lab (λ x → PE x >> q) I (λ x → PI x >> q)


mutual
  rec  : (i : Size) → {A B : Set} → (A → Process+ i (A + B)) → A → ∞Process i B
  force (rec i {A} {B} f a) j = f a >>=+ recaux j f

  recaux  : (i : Size) → {A B : Set} → (A → Process+ i (A + B)) → (A + B) → ∞Process i B
  recaux i f (inl a') = rec i f a'
  recaux i f (inr b) = delay i (terminate b)

R :  {i : Size} → {A B : Set} → (A → Process+ i (A + B)) → A → ∞Process i B
R = rec _

R' : {i : Size} → {A B : Set} → (A → Process+ i (A + B)) → (A + B) → ∞Process i B
R' = recaux _


