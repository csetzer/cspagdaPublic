{-# OPTIONS --copatterns #-}

module seq where
open import process 
open import Size
open import pro 
open ∞Process
open ∞Processx

--------------------------------------------------------       

mutual 
   _>>_ : {i : Size} →  {A : Set} → {B : Set} → ∞Process i  A  → (A → ∞Process i B) → ∞Process i B
   force (_>>_ {i} x y) j  =   _>>'_ {j} (force x j)  y

   _>>'_ : {i : Size} → {A : Set} → {B : Set} → Process i  A  → (A → ∞Process (↑ i) B) → Process i B
   node E Lab PE I PI >>' Y = node E Lab (λ x → PE x >> Y) I (λ x → PI x >> Y) 
   _>>'_ {i} (terminate x)  Y = force (Y x) i -- Y x



_∵_ : {i : Size} →
      {A : Set} →
      {B : Set} → ∞Process i A → (A → ∞Process i B) → ∞Process i B
_∵_ = _>>_ 


_∵'_ : {i : Size} →
       {A : Set} →
       {B : Set} → Process i A → (A → ∞Process (↑ i) B) → Process i B
_∵'_ =  _>>'_ 

