{-# OPTIONS --copatterns #-}
module parProof where
open import process 
open import Size
open import pro 
open ∞Process
open ∞Processx
open import renre
open import par
open import trx
open ∞Trx 
open import ind
open import ref

-------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------
                          ------------------------------------------------------------------
                          ------------------------------------------------------------------
{-
postulate eqLabel : Label → Label → Bool

EqLabel : Label → Label → Set
EqLabel l₁ l₂ = True (eqLabel l₁ l₂)

eqLabelSwap : Label → Label → Bool
eqLabelSwap l₁ l₂ = eqLabel l₂ l₁

postulate symEqLabel  : (l l' : Label) → EqLabel l l' → EqLabel l' l
postulate eqLabelIsEq : (l l' : Label) → EqLabel l l' → l == l'


lab2ff : Label → Bool
lab2ff l = ff

chooseLab₁ : (l₁ l₂ : Label) → EqLabel l₁ l₂ → Label
chooseLab₁ l₁ l₂ p = l₁

chooseLab₂ : (l₁ l₂ : Label) → EqLabel l₂ l₁ → Label
chooseLab₂ l₁ l₂ p = l₂
-}

-------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------

mutual
 refParallel : (i : Size) → {A B : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) 
            → Refinementx i {A × B} {B × A} 
               ( Parallelx i lab2ff lab2ff eqLabel     chooseLab₁ A B P Q)
               ( Parallelx i lab2ff lab2ff eqLabelSwap chooseLab₂ B A Q P)
 forcex' (refParallel i P Q l x) j  = refParallel' j (forcex P j) (forcex Q j) l (forcex' x j) 

 refParallel' : (j : Size) → {A B : Set} → (P : Processx j A) →  (Q : Processx j B) 
            → Refinementx' j {A × B} {B × A} 
               (Parallelx' j lab2ff lab2ff eqLabel chooseLab₁ A B P Q)
               (Parallelx' j lab2ff lab2ff eqLabelSwap chooseLab₂ B A Q P)
 refParallel' i (node P) (node Q) .[] empty = empty
 refParallel' i (node P) (node Q) .(node2Lab Q a :: l) (extchoice (inl (inl (sub a ()))) l x₁)
 refParallel' i (node P) (node Q) .(node2Lab P a :: l) (extchoice (inl (inr (sub a ()))) l x₁)
 refParallel' i {A} {B} (node P) (node Q) .(node2Lab P a₁ :: l) (extchoice (inr (sub (a , a₁) x))l x₁) = extchoice (inr (sub (a₁ , a) x)) l (refLemaux3 i A B P Q a a₁ x l x₁)
 refParallel' i {A} {B} (node P) (node Q) .(l :: ll) (intchoice (inl x) l ll x₁) = intchoice (inr x) l ll (Lem  i A B P Q (l :: ll) x x₁) 
 refParallel' i {A} {B} (node P) (node Q) .(l :: ll) (intchoice (inr x) l ll x₁) = intchoice (inl x) l ll (Lem₂ i A B P Q (l :: ll) x x₁)
 refParallel' i {A} {B} (node P) (terminate b) l tr =  indepFmap i A (B × A) (A × B) (_,_ b) (λ a → a , b) l (node P) tr 
 refParallel' i {A} {B} (terminate a) (node Q) l tr =  indepFmap i B (B × A) (A × B) (λ b → b , a) (_,_ a) l (node Q) tr 
 refParallel' i (terminate P) (terminate Q) .[] empty = empty 

 Lem : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l : List Label)
                    → (x₁ : ChoiceSet (node2I Q))    
                    → (tr : ∞Trx j l (parPI''' lab2ff lab2ff eqLabelSwap chooseLab₂ Q P (inl x₁)) )
                    →       ∞Trx j l (parPI''' lab2ff lab2ff eqLabel     chooseLab₁ P Q (inr x₁))
 forcex' (Lem j A B P Q l x₁ tr) j' =  refLem j j' B A Q P l x₁ (forcex' tr j')



 refLem : (j'  : Size)  → (j : Size< j') 
          → (A  B : Set) 
          → (P  : Node j' A) → (Q  : Node j' B)
          → (l  : List Label)
          → (x : ChoiceSet (node2I P))
          → (tr :  Trx j l (Parallelx' j lab2ff lab2ff eqLabelSwap chooseLab₂ A B 
                           (forcex (node2PI P x) j) (node Q) ))
          →        Trx j l (Parallelx' j lab2ff lab2ff eqLabel     chooseLab₁ B A  
                           (node Q) (forcex (node2PI P x) j))        
 refLem j j' A B P Q l x tr = refLemaux j' B A (node Q) (forcex (node2PI P x) j') l tr


 refLemaux : (j  : Size)  → (A  B : Set) → (P  : Processx j A) → (Q  : Processx j B)
                    → (l  : List Label) 
                    → (tr : Trx j l (Parallelx' j lab2ff lab2ff eqLabelSwap chooseLab₂ B A Q P))   
                    →       Trx j l (Parallelx' j lab2ff lab2ff eqLabel     chooseLab₁ A B P Q)  
 refLemaux j A B (node P) (node Q) .[] empty = empty
 refLemaux j A B (node P) (node Q) .(node2Lab Q a :: l) (extchoice (inl (inl (sub a ()))) l x₃)
 refLemaux j A B (node P) (node Q) .(node2Lab P a :: l) (extchoice (inl (inr (sub a ()))) l x₃)
 refLemaux j A B (node P) (node Q) .(node2Lab P a₁ :: l) (extchoice (inr (sub (a , a₁) x)) l x₁) = extchoice (inr (sub (a₁ , a) x)) l (refLemaux3 j A B P Q a a₁ x l x₁)
 refLemaux j A B (node P) (node Q) .(l :: ll) (intchoice (inl x) l ll x₁) = intchoice (inr x) l ll (Lem j A B P Q  (l :: ll) x x₁)
 refLemaux j A B (node P) (node Q) .(l :: ll) (intchoice (inr x) l ll x₁) = intchoice (inl x) l ll (Lem₂ j A B P Q (l :: ll) x x₁)
 refLemaux j A B (node P) (terminate b) l tr = indepFmap j A (B × A) (A × B) (_,_ b) (λ a → a , b) l (node P) tr 
 refLemaux j A B (terminate a) (node Q) l tr = indepFmap j B (B × A) (A × B) (λ b → b , a) (_,_ a) l (node Q) tr
 refLemaux j A B (terminate P) (terminate Q) .[] empty = empty


 Lem₂ : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l : List Label)
                    → (x  : ChoiceSet (node2I P))  
                    → (tr : ∞Trx j l (parPI''' lab2ff lab2ff eqLabelSwap     chooseLab₂  Q P (inr x)) ) 
                          → ∞Trx j l (parPI''' lab2ff lab2ff eqLabel         chooseLab₁  P Q (inl x))
 forcex' (Lem₂ j A B P Q l x tr) j' =  refLem₂ j j' B A Q P l x (forcex' tr j')

 refLem₂ : (j'  : Size)  → (j : Size< j')
        → (A  B : Set)
        → (P  : Node j' A) → (Q  : Node j' B) 
        → (l  : List Label)
        → (x  : ChoiceSet (node2I Q))
        → (tr : Trx j l (Parallelx' j lab2ff lab2ff eqLabelSwap chooseLab₂ A B (node P) (forcex (node2PI Q x) j) ))
        →   Trx j l     (Parallelx' j lab2ff lab2ff eqLabel chooseLab₁ B A (forcex (node2PI Q x) j) (node P))
 refLem₂ j j' A B P Q l x tr = refLemaux j' B A (forcex (node2PI Q x) j') (node P) l tr


 refLemaux3 : (j  : Size) → (A B : Set) → (P  : Node j A) → (Q  : Node j B) 
              →  (a  : ChoiceSet (node2E Q)) → (a₁ : ChoiceSet (node2E P))
              →  (x  : True (eqLabelSwap (node2Lab Q a) (node2Lab P a₁)))
              →  (l  : List Label)
              → ∞Trx j l (parPEE' lab2ff lab2ff eqLabelSwap chooseLab₂ Q P  (inr (sub (a , a₁) x)))
              → ∞Trx j l (parPEE' lab2ff lab2ff eqLabel chooseLab₁ P Q  (inr (sub (a₁ , a) x)))
 forcex' (refLemaux3 j A B (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁) a a₁ x l tr) j' = refParallel' j' (forcex (PE a₁) j') (forcex (PE₁ a) j') l (forcex' tr j')







----------------------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------------

mutual
 TraPar : (i : Size) → {A B C : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) → (Z : ∞Processx i C) 
            → Refinementx i {((A × B) × C)}  {(A × (B × C))}
           (Parallelx i lab2ff lab2ff eqLabel chooseLab₁ (A × B) C (Parallelx i lab2ff lab2ff eqLabel chooseLab₁ A B P Q) Z)
           (Parallelx i lab2ff lab2ff eqLabel chooseLab₁ A (B × C) P (Parallelx i lab2ff lab2ff eqLabel chooseLab₁ B C Q Z))

 forcex' (TraPar i P Q Z l x) j  = TraPar' j (forcex P j) (forcex Q j) (forcex Z j) l (forcex' x j) 

 TraPar' : (j : Size) → {A B C : Set} → (P : Processx j A) →  (Q : Processx j B) →  (Z : Processx j C)
            → Refinementx' j {((A × B) × C)}  {(A × (B × C))}
            (Parallelx' j lab2ff lab2ff eqLabel chooseLab₁ (A × B) C (Parallelx' j lab2ff lab2ff eqLabel chooseLab₁ A B P Q) Z)
            (Parallelx' j lab2ff lab2ff eqLabel chooseLab₁ A (B × C) P (Parallelx' j lab2ff lab2ff eqLabel chooseLab₁ B C Q Z))

 TraPar' i (node x) (node x₁) (node x₂) .[] empty = empty
 TraPar' i (node P) (node Q) (node Z) .(node2Lab P a :: l) (extchoice (inl (inl (sub a ()))) l x₁)
 TraPar' i (node P) (node Q) (node Z) ._ (extchoice (inl (inr (sub a ()))) l x₁)
 TraPar' i (node P) (node Q) (node Z) .(node2Lab P a :: l) (extchoice (inr (sub (a , a₁) x)) l x₁) = {!!}
 TraPar' i (node P) (node Q) (node Z) .(l :: ll) (intchoice (inl x) l ll x₁) = {!!}
 TraPar' i (node P) (node Q) (node Z) .(l :: ll) (intchoice (inr (inl x)) l ll x₁) = {!!}
 TraPar' i (node P) (node Q) (node Z) .(l :: ll) (intchoice (inr (inr x)) l ll x₁) = {!!}
 TraPar' i (node P) (node Q) (terminate Z) .[] empty = empty
 TraPar' i (node P) (node Q) (terminate Z) .(node2Lab P a :: l) (extchoice (inl (inl (sub a ()))) l x₁)
 TraPar' i (node P) (node Q) (terminate Z) ._ (extchoice (inl (inr (sub a ()))) l x₁)
 TraPar' i {A} {B} {C} (node P) (node Q) (terminate Z) .(node2Lab P a :: l) (extchoice (inr (sub (a , a₁) x)) l x₁) = {!!}
 TraPar' i (node P) (node Q) (terminate Z) .(l :: ll) (intchoice (inl x) l ll x₁) = {!!}
 TraPar' i (node P) (node Q) (terminate Z) .(l :: ll) (intchoice (inr x) l ll x₁) = {!!}
 TraPar' i (node P) (terminate Q) (node Z) .[] empty = empty
 TraPar' i (node P) (terminate Q) (node Z) .(node2Lab P a :: l) (extchoice (inl (inl (sub a ()))) l x₁)
 TraPar' i (node P) (terminate Q) (node Z) .(node2Lab (fmapx'' i (_,_ Q) Z) a :: l) (extchoice (inl (inr (sub a ()))) l x₁)
 TraPar' i (node P) (terminate Q) (node Z) .(node2Lab P a :: l) (extchoice (inr (sub (a , a₁) x)) l x₁) = {!x!}
 TraPar' i (node P) (terminate Q) (node Z) .(l :: ll) (intchoice (inl x) l ll x₁) = intchoice (inl {!x!}) l ll {!!}
 TraPar' i (node P) (terminate Q) (node Z) .(l :: ll) (intchoice (inr x) l ll x₁) = {!!}
 TraPar' i (node P) (terminate Q) (terminate Z) .[] empty = empty
 TraPar' i (node (thenode E Lab PE I PI)) (terminate Q) (terminate Z) .(Lab x :: l) (extchoice x l x₁) = {!!}
 TraPar' i (node P) (terminate Q) (terminate Z) .(l :: ll) (intchoice x l ll x₁) = {!!}
 TraPar' i (terminate P) (node Q) (node Z) .[] empty = empty
 TraPar' i (terminate P) (node Q) (node Z) .(node2Lab Q a :: l) (extchoice (inl (inl (sub a ()))) l x₁)
 TraPar' i (terminate P) (node Q) (node Z) .(node2Lab Z a :: l) (extchoice (inl (inr (sub a ()))) l x₁)
 TraPar' i (terminate P) (node Q) (node Z) .(node2Lab Q a :: l) (extchoice (inr (sub (a , a₁) x)) l x₁) = {!!}
 TraPar' i (terminate P) (node Q) (node Z) .(l :: ll) (intchoice (inl x) l ll x₁) = {!!}
 TraPar' i (terminate P) (node Q) (node Z) .(l :: ll) (intchoice (inr x) l ll x₁) = {!!}
 TraPar' i {A} {B} {C} (terminate P) (node Q) (terminate Z) l tr = indepFmap i (A × B) C ((A × B) × C) (λ x → Z) (λ a → a , Z) l (node (fmapx'' i (_,_ P) Q)) {!!}
 TraPar' i {A} {B} {C} (terminate P) (terminate Q) (node Z) l tr = indepFmap i C (A × (B × C)) ((A × B) × C) (λ x → P , (Q , x)) (_,_ (P , Q)) l (node Z) {!!}
 TraPar' i (terminate P) (terminate Q) (terminate Z) .[] empty = empty

{-
 refLemaux j A B (node P) (terminate b) l tr = indepFmap j A (B × A) (A × B) (_,_ b) (λ a → a , b) l (node P) tr 
 refLemaux j A B (terminate a) (node Q) l tr = indepFmap j B (B × A) (A × B) (λ b → b , a) (_,_ a) l (node Q) tr
 indepFmap i (A × B) C ((A × B) × C) {!((A × (B × C))!} (λ a₂ → a₂ , Z) (node2Lab (thenode (parE lab2ff lab2ff eqLabel chooseLab₁ P (fmapx'' i (λ a₂ → a₂ , Z) Q)) (parPEE' lab2ff lab2ff eqLabel chooseLab₁ P (fmapx'' i (λ a₂ → a₂ , Z) Q))                                                               (I'' P (fmapx'' i (λ a₂ → a₂ , Z) Q))                                                              (parPI''' lab2ff lab2ff eqLabel chooseLab₁ P (fmapx'' i (λ a₂ → a₂ , Z) Q))) (inr (sub (a , a₁) x)) :: l) (node
                                                  (thenode (parE lab2ff lab2ff eqLabel chooseLab₁ P Q)
                                                           (parLab' lab2ff lab2ff eqLabel chooseLab₁ P Q)                                                                                    (λ z → parPEE' lab2ff lab2ff eqLabel chooseLab₁ P Q z) (I'' P Q)                                                                         (λ z → parPI''' lab2ff lab2ff eqLabel chooseLab₁ P Q z))) {!!}





 indepFmap i (A × B) C ((A × B) × C) (λ x₂ → Z) (λ a₂ → a₂ , Z) (node2Lab
                                                                                                                                                                                    (thenode
                                                                                                                                                                                     (parE lab2ff lab2ff eqLabel chooseLab₁ P
                                                                                                                                                                                      (fmapx'' i (λ a₂ → a₂ , Z) Q))
                                                                                                                                                                                     (parLab' lab2ff lab2ff eqLabel chooseLab₁ P
                                                                                                                                                                                      (fmapx'' i (λ a₂ → a₂ , Z) Q))
                                                                                                                                                                                     (parPEE' lab2ff lab2ff eqLabel chooseLab₁ P
                                                                                                                                                                                      (fmapx'' i (λ a₂ → a₂ , Z) Q))
                                                                                                                                                                                     (I'' P (fmapx'' i (λ a₂ → a₂ , Z) Q))
                                                                                                                                                                                     (parPI''' lab2ff lab2ff eqLabel chooseLab₁ P
                                                                                                                                                                                      (fmapx'' i (λ a₂ → a₂ , Z) Q)))
                                                                                                                                                                                    (inr (sub (a , a₁) x))
                                                                                                                                                                                    :: l) (node
                                                                                                                                                                              (thenode (parE lab2ff lab2ff eqLabel chooseLab₁ P Q)
                                                                                                                                                                               (parLab' lab2ff lab2ff eqLabel chooseLab₁ P Q)
                                                                                                                                                                               (λ z → parPEE' lab2ff lab2ff eqLabel chooseLab₁ P Q z) (I'' P Q)
                                                                                                                                                                               (λ z → parPI''' lab2ff lab2ff eqLabel chooseLab₁ P Q z))) (forcex' {!!} {!!})




mutual
 TraPar : (i : Size) → {A B C : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) → (Z : ∞Processx i C) 
            → Refinementx i {((A × B) × C)}  {(A × (B × C))}
           (Parallelx i lab2ff lab2ff eqLabel chooseLab₁ (A × B) C (Parallelx i lab2ff lab2ff eqLabel chooseLab₁ A B P Q) Z)
           (Parallelx i lab2ff lab2ff eqLabel chooseLab₁ A (B × C) P (Parallelx i lab2ff lab2ff eqLabel chooseLab₁ B C Q Z))

 forcex' (TraPar i P Q Z l x) j  = TraPar' j (forcex P j) (forcex Q j) (forcex Z j) l (forcex' x j) 

 TraPar' : (j : Size) → {A B C : Set} → (P : Processx j A) →  (Q : Processx j B) →  (Z : Processx j C)
            → Refinementx' j {((A × B) × C)}  {(A × (B × C))}
            (Parallelx' j lab2ff lab2ff eqLabel chooseLab₁ (A × B) C (Parallelx' j lab2ff lab2ff eqLabel chooseLab₁ A B P Q) Z)
            (Parallelx' j lab2ff lab2ff eqLabel chooseLab₁ A (B × C) P (Parallelx' j lab2ff lab2ff eqLabel chooseLab₁ B C Q Z))

 TraPar' i (node x) (node x₁) (node x₂) .[] empty = empty
 TraPar' i (node P) (node Q) (node Z) .(node2Lab P a :: l) (extchoice (inl (inl (sub a ()))) l x₁)
 TraPar' i (node P) (node Q) (node Z) ._ (extchoice (inl (inr (sub a ()))) l x₁)
 TraPar' i (node P) (node Q) (node Z) .(node2Lab P a :: l) (extchoice (inr (sub (a , a₁) x)) l x₁) = {!!}
 TraPar' i (node P) (node Q) (node Z) .(l :: ll) (intchoice (inl x) l ll x₁) = {!!}
 TraPar' i (node P) (node Q) (node Z) .(l :: ll) (intchoice (inr (inl x)) l ll x₁) = {!!}
 TraPar' i (node P) (node Q) (node Z) .(l :: ll) (intchoice (inr (inr x)) l ll x₁) = {!!}
 TraPar' i (node P) (node Q) (terminate Z) .[] empty = empty
 TraPar' i (node P) (node Q) (terminate Z) .(node2Lab P a :: l) (extchoice (inl (inl (sub a ()))) l x₁)
 TraPar' i (node P) (node Q) (terminate Z) ._ (extchoice (inl (inr (sub a ()))) l x₁)
 TraPar' i {A} {B} {C} (node P) (node Q) (terminate Z) .(node2Lab P a :: l) (extchoice (inr (sub (a , a₁) x)) l x₁) = {!!}
 TraPar' i (node P) (node Q) (terminate Z) .(l :: ll) (intchoice (inl x) l ll x₁) = {!!}
 TraPar' i (node P) (node Q) (terminate Z) .(l :: ll) (intchoice (inr x) l ll x₁) = {!!}
 TraPar' i (node P) (terminate Q) (node Z) .[] empty = empty
 TraPar' i (node P) (terminate Q) (node Z) .(node2Lab P a :: l) (extchoice (inl (inl (sub a ()))) l x₁)
 TraPar' i (node P) (terminate Q) (node Z) .(node2Lab (fmapx'' i (_,_ Q) Z) a :: l) (extchoice (inl (inr (sub a ()))) l x₁)
 TraPar' i (node P) (terminate Q) (node Z) .(node2Lab P a :: l) (extchoice (inr (sub (a , a₁) x)) l x₁) = {!x!}
 TraPar' i (node P) (terminate Q) (node Z) .(l :: ll) (intchoice (inl x) l ll x₁) = {!!}
 TraPar' i (node P) (terminate Q) (node Z) .(l :: ll) (intchoice (inr x) l ll x₁) = {!!}
 TraPar' i (node P) (terminate Q) (terminate Z) .[] empty = empty
 TraPar' i (node (thenode E Lab PE I PI)) (terminate Q) (terminate Z) .(Lab x :: l) (extchoice x l x₁) = {!!}
 TraPar' i (node P) (terminate Q) (terminate Z) .(l :: ll) (intchoice x l ll x₁) = {!!}
 TraPar' i (terminate P) (node Q) (node Z) .[] empty = empty
 TraPar' i (terminate P) (node Q) (node Z) .(node2Lab Q a :: l) (extchoice (inl (inl (sub a ()))) l x₁)
 TraPar' i (terminate P) (node Q) (node Z) .(node2Lab Z a :: l) (extchoice (inl (inr (sub a ()))) l x₁)
 TraPar' i (terminate P) (node Q) (node Z) .(node2Lab Q a :: l) (extchoice (inr (sub (a , a₁) x)) l x₁) = {!!}
 TraPar' i (terminate P) (node Q) (node Z) .(l :: ll) (intchoice (inl x) l ll x₁) = {!!}
 TraPar' i (terminate P) (node Q) (node Z) .(l :: ll) (intchoice (inr x) l ll x₁) = {!!}
 TraPar' i (terminate P) (node Q) (terminate Z) .[] empty = empty
 TraPar' i (terminate P) (node (thenode E Lab PE I PI)) (terminate Z) .(Lab x :: l) (extchoice x l x₁) = {!!}
 TraPar' i (terminate P) (node Q) (terminate Z) .(l :: ll) (intchoice x l ll x₁) = {!!}
 TraPar' i (terminate P) (terminate Q) (node Z) .[] empty = empty
 TraPar' i (terminate P) (terminate Q) (node (thenode E Lab PE I PI)) .(Lab x :: l) (extchoice x l x₁) = {!!}
 TraPar' i {A} {B} {C} (terminate P) (terminate Q) (node Z) .(l :: ll) (intchoice x l ll x₁) = indepFmap i C (A × (B × C)) ((A × B) × C) (λ x₂ → P , (Q , x₂)) (_,_ (P , Q)) (l :: ll) (node Z) {!!}
 TraPar' i (terminate P) (terminate Q) (terminate Z) .[] empty = empty






-}
