module ref where
open import Size
open import process
open import pro 
open ∞Process
open ∞Processx
open import trx
open ∞Trx

Refinementx : (i : Size) {A B : Set} (p : ∞Processx i A) (p' : ∞Processx i B) → Set
Refinementx i p p'  = (l : List Label) →  ∞Trx i l p'  → ∞Trx i l p

_⊑_ : {i : Size} {A B : Set} (p : ∞Processx i A) (p' : ∞Processx i B) → Set
_⊑_ = Refinementx _ 


Refinementx' : (j : Size) {A B : Set} (p : Processx j A) (p' : Processx j B) → Set
Refinementx' j p p'  = (l : List Label) → Trx j l p' → Trx j l p

_⊑'_ :  {j : Size} {A B : Set} (p : Processx j A) (p' : Processx j B) → Set
_⊑'_ = Refinementx' _


