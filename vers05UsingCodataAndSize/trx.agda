module trx where 
open import Size
open import process
open import pro
open ∞Process
open ∞Processx

-------------------------- Refinment---------------------
mutual
   
    record ∞Trx (i : Size) {A : Set} (l : List Label) (P : ∞Processx  i A) : Set where
     constructor delayTrx
     coinductive
     field
       forcex' : (j : Size< i) → Trx j  l (forcex P j)

    data Trx (j : Size) {A : Set} : (l : List Label) → (P : Processx j A) → Set where 
        empty : {P : Processx j A} → Trx  j {A} [] P
        extchoice : {P  : Node j A}
         → (x : Node2E P)
         → (l : List Label)
         → ∞Trx j {A} l (node2PE P x)
         → Trx j {A} ((node2Lab P x) :: l) (node P)
        intchoice : {P  : Node j A}
         → (x : Node2I P)
         → (l : Label)
         → (ll : List Label)
         → ∞Trx j {A} (l :: ll) (node2PI P x)
         → Trx  j {A} (l :: ll)  (node P)


open ∞Trx


lemmaTrx : (i : Size) {A B : Set} (l : List Label) (P : ∞Processx  i A)(Q : ∞Processx  i B)
           (f : {j : Size< i} → Trx j {A} l (forcex P j) -> Trx j {B} l (forcex Q j) )
           → ∞Trx i {A} l P → ∞Trx i {B} l Q
forcex' (lemmaTrx i {A} {B} l P Q f tr') j = f {j} (forcex' tr' j)
