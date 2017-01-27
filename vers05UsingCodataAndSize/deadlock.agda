--{-# OPTIONS --copatterns #-}

module deadlock where
open import process 
open import Size
open import pro 
open ∞Processx
open ∞Process
--------------------------------------------------------       
----------------- Deadlock -----------------------


Deadlock : (i : Size) → {A : Set} →  ∞Process i A
force (Deadlock i) j = node ∅' efq efq ∅' efq


