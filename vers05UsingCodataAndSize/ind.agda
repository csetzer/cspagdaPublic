module ind where
open import Size 
open import process
open import pro
open ∞Process
open ∞Processx
open import trx
open ∞Trx
open import renre


mutual
  indepFmap :  (j : Size) → (A B C : Set) → (f : A → B) → (g : A → C) → (l : List Label) → (P : Processx j A) → 
               Trx j l (fmapx' j f P) →  Trx j l (fmapx' j g P)
 

  indepFmap j A B C f g .[] (node (thenode E Lab PE I PI)) empty = empty
  indepFmap j A B C f g .(Lab x :: l) (node (thenode E Lab PE I PI)) (extchoice x l x₁) =  extchoice x l (indepFmapx j A B C f g l (PE x) x₁)
  indepFmap j A B C f g .(l :: ll) (node (thenode E Lab PE I PI)) (intchoice x l ll x₁) =  intchoice x l ll (indepFmapx j A B C f g (l :: ll) (PI x) x₁)
  indepFmap j A B C f g .[] (terminate x) empty = empty              

  indepFmapx :  (j : Size) → (A B C : Set) → (f : A → B) → (g : A → C) → (l : List Label) → (P : ∞Processx j A) → 
               ∞Trx j l (fmapx j f P) →  ∞Trx j l (fmapx j g P)
  forcex' (indepFmapx j A B C f g l P tr) j'  = indepFmap j' A B C f g l (forcex P j') (forcex' tr j')




mutual
  indepFmap' :  (j : Size) → {A B C : Set} → {f : A → B} → {g : A → C} → (l : List Label) → (P : Processx j A) → 
               Trx j l (fmapx' j f P) →  Trx j l (fmapx' j g P)
 

  indepFmap' j {A} {B} {C} {f} {g} .[] (node (thenode E Lab PE I PI)) empty = empty
  indepFmap' j {A} {B} {C} {f} {g} .(Lab x :: l) (node (thenode E Lab PE I PI)) (extchoice x l x₁) =  extchoice x l (indepFmapx j A B C f g l (PE x) x₁)
  indepFmap' j {A} {B} {C} {f} {g} .(l :: ll) (node (thenode E Lab PE I PI)) (intchoice x l ll x₁) =  intchoice x l ll (indepFmapx j A B C f g (l :: ll) (PI x) x₁)
  indepFmap' j {A} {B} {C} {f} {g} .[] (terminate x) empty = empty              
