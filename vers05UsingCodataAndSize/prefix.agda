{-# OPTIONS --copatterns #-}

module prefix where
open import process 
open import Size
open import pro 
open Process
open Processx
open ∞Process
open ∞Processx 

---------------------------  Prefix -------------------

_⟶_ : {i : Size} → {A : Set} → Label → ∞Process i A → ∞Process (↑ i) A 
force (_⟶_ {i} a P) j = node ⊤' (λ x → a) (λ x → P) ∅' efq



_⟶'_ : {i : Size} → {A : Set} → Label → ∞Processx i A → ∞Processx (↑ i) A 
forcex (_⟶'_ {i} a P) j = node (thenode ⊤' (λ x → a) (λ x → P) ∅' efq)


_⟶∞_ : {i : Size} → {A : Set} → Label → Processx i A → Processx (↑ i) A 
_⟶∞_ {i} a P = node (thenode ⊤' (λ x → a) (λ x → delayx i P) ∅' efq) 
