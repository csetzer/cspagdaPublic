{-# OPTIONS --copatterns #-}

module stop where
open import process 
open import Size
open import pro 
open ∞Process
open ∞Processx


--------------- Stop Operation ------------------


STOP : (i : Size) → {A : Set} →  A → ∞Process i A
force (STOP i a) j =  terminate a


Stop :  {i : Size} → {A : Set} →  A → ∞Process i A
Stop = STOP _


STOP' : (i : Size) → {A : Set} →  A → ∞Processx i A
forcex (STOP' i a) j =  terminate a


Stop' :  {i : Size} → {A : Set} →  A → ∞Processx i A
Stop' = STOP' _

∞STOP : (i : Size) → {A : Set} →  A → Processx i A
∞STOP i a =  terminate a


∞Stop :  {i : Size} → {A : Set} →  A → Processx i A
∞Stop = ∞STOP _

