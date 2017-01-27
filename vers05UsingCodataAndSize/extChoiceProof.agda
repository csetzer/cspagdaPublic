{-# OPTIONS --copatterns #-}

module extChoiceProof where
open import process 
open import Size
open import pro
open ∞Process
open ∞Processx
open import renre
open import extchoice
open import stop
open import trx
open ∞Trx 
open import ref
open import ind

------------------------------------------------------------------------------------------------------------------------
-----------------------------------ProofTheProaritesOfreflextyOfExternalChoice------------------------------------------
------------------------------------------------------------------------------------------------------------------------



mutual
 refExtChoice : (i : Size) → {A B : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) 
            → Refinementx i {(A + B) + (A × B)} {(B + A) + (B × A)} (extChx i P Q) (extChx i Q P) 

 forcex' ( refExtChoice i P Q l x) j  =  refExtChoice' j (forcex P j) (forcex Q j) l (forcex' x j) 

 refExtChoice' : (j : Size) → {A B : Set} → (P : Processx j A) →  (Q : Processx j B) 
            → Refinementx' j {(A + B) + (A × B)} {(B + A) + (B × A)} (extChx' j P Q) (extChx' j Q P) 


 refExtChoice' j {A} {B} (node P) (node Q) [] empty = empty
 refExtChoice' j {A} {B} (node P) (node Q) (.(node2Lab Q x) :: l) (extchoice (inl x) .l tr) =  extchoice (inr x) l (refExtChoiceLem1 j A B P Q l x tr)
 refExtChoice' j {A} {B} (node P) (node Q) (.(node2Lab P x) :: l) (extchoice (inr x) .l tr) = extchoice (inl x) l (refExtChoiceLem2 j B A Q P l x tr)
 refExtChoice' j {A} {B} (node P) (node Q) (l₁ :: l) (intchoice (inl x) .l₁ .l x₁) = intchoice (inr x) l₁ l (refExtChoiceLem3 j A B P Q (l₁ :: l) x x₁)
 refExtChoice' j {A} {B} (node P) (node Q) (l₁ :: l) (intchoice (inr x) .l₁ .l x₁) = intchoice (inl x) l₁ l (refExtChoiceLem4 j B A Q P (l₁ :: l) x x₁)
 refExtChoice' j (node P) (terminate Q) [] tr = empty
 refExtChoice' j (node (thenode E Lab PE I PI)) (terminate Q) (x :: x₁) ()
 refExtChoice' j (terminate x) (node x₁) [] empty = empty
 refExtChoice' j (terminate x) (node (thenode E Lab PE I PI)) (x₂ :: x₃) ()
 refExtChoice' j (terminate x) (terminate x₁) .[] empty = empty

 refExtChoiceLem1 : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l  : List Label)
                    → (x  : ChoiceSet (node2E Q))
                    → (tr : ∞Trx j l (extChPE' Q P (inl x))) 
                    → ∞Trx j l (extChPE' P Q (inr x))
 forcex' (refExtChoiceLem1 j A B P Q l x tr) j' = indepFmap j' B  ((B + A) + (B × A)) ((A + B) + (A × B)) (inl ∘ inl) (inl ∘ inr) l (forcex (node2PE Q x) j') (forcex' tr j')

 refExtChoiceLem2xx : (j  : Size)  → (A  B : Set) → (P  : Processx j A) → (Q  : Processx j B)  → (l  : List Label) 
                    → (tr : Trx j l (extChx' j P Q))
                    →       Trx j l (extChx' j Q P) 
 refExtChoiceLem2xx j A B (node P) (node Q) l tr = refExtChoiceLem2xxx j B A (node Q) (node P) l tr
 refExtChoiceLem2xx j A B (node (thenode E Lab PE I PI)) (terminate x₁) .[] empty = empty
 refExtChoiceLem2xx j A B (terminate x) (node (thenode E Lab PE I PI)) .[] empty = empty
 refExtChoiceLem2xx j A B (terminate x) (terminate x₁) .[] empty = empty

 refExtChoiceLem2xxx : (j  : Size)  → (A  B : Set) → (P  : Processx j A) → (Q  : Processx j B)
                    → (l  : List Label) 
                    → (tr : Trx j l (extChx' j Q P))
                    →       Trx j l (extChx' j P Q) 

 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .[] empty = empty
 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(Lab₁ x :: l) (extchoice (inl x) l x₁) = extchoice (inr x) l (refExtChoiceLem1 _ _ _ (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁) l x x₁)
 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(Lab x :: l) (extchoice (inr x) l x₁) = extchoice (inl x) l (refExtChoiceLem2 _ _ _ (thenode E₁ Lab₁ PE₁ I₁ PI₁) (thenode E Lab PE I PI) l x x₁)
 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(l :: ll) (intchoice (inl x) l ll x₁) = intchoice (inr x) l ll (refExtChoiceLem3 _ _ _ (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁) (l :: ll) x x₁)
 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(l :: ll) (intchoice (inr x) l ll x₁) = intchoice (inl x) l ll (refExtChoiceLem4 _ _ _ (thenode E₁ Lab₁ PE₁ I₁ PI₁) (thenode E Lab PE I PI) (l :: ll) x x₁) 
 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (terminate x₁) .[] empty = empty
 refExtChoiceLem2xxx j A B (terminate x) (node (thenode E Lab PE I PI)) .[] empty = empty
 refExtChoiceLem2xxx j A B (terminate x) (terminate x₁) .[] empty = empty

 refExtChoiceLem2x : (j'  : Size)  → (j : Size< j') → (A  B : Set) → (P  : Node j' A) → (Q  : Node j' B) 
                    → (l  : List Label)
                    → (x  : ChoiceSet (node2I Q))
                    → (tr : Trx j l (extChx' j (node P) (forcex (node2PI Q x) j))) -- (forcex (extChPI' P Q (inr x)) j)
                    →       Trx j l (extChx' j (forcex (node2PI Q x) j) (node P))  -- (forcex (extChPI' Q P (inl x)) j)
 refExtChoiceLem2x j j' A B P Q l x tr =  refExtChoiceLem2xx j' A B (node P) (forcex (node2PI Q x) j') l tr

 refExtChoiceLem2x''' : (j'  : Size)  → (j : Size< j') → (A  B : Set) → (P  : Node j' A) → (Q  : Node j' B)
                    → (l  : List Label)
                    → (x : ChoiceSet (node2I P))
                    → (tr :  Trx j l (extChx' j (forcex (node2PI P x) j) (node Q))) 
                    →        Trx j l (extChx' j (node Q) (forcex (node2PI P x) j))  
 refExtChoiceLem2x''' j j' A B P Q l x tr = refExtChoiceLem2xxx j' B A (node Q) (forcex (node2PI P x) j') l tr


 refExtChoiceLem2 : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l  : List Label)
                    → (x  : ChoiceSet (node2E Q))
                    → (tr : ∞Trx j l (extChPE' P Q (inr x))) 
                    → ∞Trx j l (extChPE' Q P (inl x))
 forcex' (refExtChoiceLem2 j A B P Q l x tr) j' = indepFmap j' B ((A + B) + (A × B)) ((B + A) + (B × A)) (inl ∘ inr) (inl ∘ inl) l (forcex  (node2PE Q x) j') (forcex' tr j')


 refExtChoiceLem3 : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l : List Label)
                    → (x  : ChoiceSet (node2I Q))
                    → (tr : ∞Trx j l (extChPI' Q P (inl x))) 
                    → ∞Trx j l (extChPI' P Q (inr x))
 forcex' (refExtChoiceLem3 j A B P Q l x tr) j' = refExtChoiceLem2x''' j j' B A Q P l x (forcex' tr j')

 refExtChoiceLem4 : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l : List Label)
                    → (x  : ChoiceSet (node2I Q))
                    → (tr : ∞Trx j l (extChPI' P Q (inr x))) 
                    → ∞Trx j l (extChPI' Q P (inl x))
 forcex' (refExtChoiceLem4 j A B P Q l x tr) j' = refExtChoiceLem2x j j' A B P Q l x (forcex' tr j') 


------------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------------


mutual
 ExtChoice'' : (i : Size) → {A B : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) 
            → (P □ Q) ⊑ (Q □ P) 

 forcex' ( ExtChoice'' i P Q l x) j  =  ExtChoice''' j (forcex P j) (forcex Q j) l (forcex' x j) 

 ExtChoice''' : (j : Size) → {A B : Set} → (P : Processx j A) →  (Q : Processx j B) 
            → (P □' Q) ⊑' (Q □' P) 


 ExtChoice''' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .[] empty = empty
 ExtChoice''' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(Lab₁ x :: l) (extchoice (inl x) l x₁) = extchoice (inr x) l (refExtChoiceLem1 j _ _ (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁) l x x₁)
 ExtChoice''' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(Lab x :: l) (extchoice (inr x) l x₁) = extchoice (inl x) l (refExtChoiceLem2 j _ _ (thenode E₁ Lab₁ PE₁ I₁ PI₁) (thenode E Lab PE I PI) l x x₁)
 ExtChoice''' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(l :: ll) (intchoice (inl x) l ll x₁) = intchoice (inr x) l ll (refExtChoiceLem3 j _ _ (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁) (l :: ll) x x₁)
 ExtChoice''' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(l :: ll) (intchoice (inr x) l ll x₁) = intchoice (inl x) l ll (refExtChoiceLem4 j _ _ (thenode E₁ Lab₁ PE₁ I₁ PI₁) (thenode E Lab PE I PI) (l :: ll) x x₁)
 ExtChoice''' j (node (thenode E Lab PE I PI)) (terminate Q) .[] empty = empty
 ExtChoice''' j (terminate P) (node (thenode E Lab PE I PI)) .[] empty = empty
 ExtChoice''' j (terminate P) (terminate x) .[] empty = empty







-------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------


mutual
 TraExt : (i : Size) → {A B C : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) → (Z : ∞Processx i C)
            → (P □ (Q □ Z)) ⊑ ((P □ Q) □ Z) 

 forcex' ( TraExt i P Q Z l x) j  =  TraExt' j (forcex P j) (forcex Q j) (forcex Z j) l (forcex' x j) 

 TraExt' : (j : Size) → {A B C : Set} → (P : Processx j A) →  (Q : Processx j B)  → (Z : Processx j C)
             → (P □' (Q □' Z)) ⊑' ((P □' Q) □' Z) 

 TraExt' j P Q Z [] empty = empty
 TraExt' j (node P) (node Q) (node Z) (.(node2Lab P x) :: l) (extchoice (inl (inl x)) .l x₁) = extchoice (inl x) l (TraExt'aux j P Q Z l x x₁)
 TraExt' j (node P) (node Q) (node Z) (.(node2Lab Q x) :: l) (extchoice (inl (inr x)) .l x₁) = extchoice (inr (inl x)) l (TraExt'aux₁ j P Q Z l x x₁)
 TraExt' j (node P) (node Q) (node Z) (.(node2Lab Z x) :: l) (extchoice (inr x) .l x₁) = extchoice (inr (inr x)) l (TraExt'aux₂ j P Q Z l x x₁)
 TraExt' j (node P) (node Q) (node Z) (l₁ :: l) (intchoice (inl (inl x)) .l₁ .l x₁) = intchoice (inl x) l₁ l  (TraExt'aux₃ j P Q Z (l₁ :: l) x x₁)
 TraExt' j (node P) (node Q) (node Z) (l₁ :: l) (intchoice (inl (inr x)) .l₁ .l x₁) = intchoice (inr (inl x)) l₁ l (TraExt'aux₄ j P Q Z (l₁ :: l) x x₁) 
 TraExt' j (node P) (node Q) (node Z) (l₁ :: l) (intchoice (inr x) .l₁ .l x₁) = intchoice (inr (inr x)) l₁ l (TraExt'aux₅ j  P Q Z (l₁ :: l) x x₁)
 TraExt' j (node P) (node Q) (terminate Z) (a :: l) ()
 TraExt' j (node (thenode E Lab PE I PI)) (terminate Q) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) (a :: l) ()
 TraExt' j (node (thenode E Lab PE I PI)) (terminate Q) (terminate Z) (a :: l) ()
 TraExt' j (terminate P) (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) (a :: l) ()
 TraExt' j (terminate P) (node (thenode E Lab PE I PI)) (terminate Z) (a :: l) ()
 TraExt' j (terminate P) (terminate Q) (node (thenode E Lab PE I PI)) (a :: l) ()
 TraExt' j (terminate P) (terminate Q) (terminate Z) (a :: l) ()



 TraExt'aux : (j  : Size) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2E P)) 
              → (x₁ : ∞Trx j l (extChPE' (extChNode P Q) Z (inl (inl x)))) 
              → ∞Trx j l (extChPE' P (extChNode Q Z) (inl x))
 forcex' (TraExt'aux j {A} {B} {C}  P Q Z l x x₁) j' = {!!} -- indepFmap j' A ((((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C)) ((A + ((B + C) + (B × C))) + (A × ((B + C) + (B × C)))) {!!} (inl ∘ inl) l (forcex (node2PE P x) j') {!!} -- LemTraExt'aux j j' P Q Z l x x₁


{-
      (j : Size) (A B C : Set) (P : Processx j A)
      (Q : Processx j B) (Z : Processx j C) (l : List Label) →
      Trx j {(((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C)} l
      (extChx' j {(A + B) + (A × B)} {C} (extChx' j {A} {B} P Q) Z) →
      Trx j {(A + ((B + C) + (B × C))) + (A × ((B + C) + (B × C)))} l
      (extChx' j {A} {(B + C) + (B × C)} P (extChx' j {B} {C} Q Z))
-}

{-
 LemTraExt'aux : (j  : Size) → (j' : Size< j) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2E P)) 
              → (x₁ : ∞Trx j l (extChPE' (extChNode P Q) Z (inl (inl x)))) 
              →  Trx j' l (fmapx' j' (inl ∘ inl) (forcex (node2PE P x) j'))
 LemTraExt'aux j j' {A} {B} {C}  P Q Z l x x₁ = {!!} -- refLemTraExt'aux₅' j' A B C {!(forcex (node2PE P x) j')!} (node Q) (node Z) l (forcex' x₁ j')
-}
 TraExt'aux₁ : (j  : Size) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2E Q)) 
              → (x₁ : ∞Trx j l (extChPE' (extChNode P Q) Z (inl (inr x)))) 
              → ∞Trx j l (extChPE' P (extChNode Q Z) (inr (inl x)))
 forcex' (TraExt'aux₁ j {A} {B} {C} P Q Z l x x₁) j' = {!!} -- indepFmap j' ((B + C) + (B × C)) ((((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C)) ((A + ((B + C) + (B × C))) + (A × ((B + C) + (B × C)))) {!!} (inl ∘ inr) l (fmapx' j' (inl ∘ inl) (forcex (node2PE Q x) j')) {!!} 
 -- LemTraExt'aux₁ j j' P Q Z l x x₁ 
{-
 LemTraExt'aux₁ : (j  : Size) → (j' : Size< j) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2E Q)) 
              → (x₁ : ∞Trx j l (extChPE' (extChNode P Q) Z (inl (inr x))))
              →  Trx j' l (fmapx' j' (inl ∘ inr) (fmapx' j' (inl ∘ inl) (forcex (node2PE Q x) j')))
 LemTraExt'aux₁ j j' {A} {B} {C}  P Q Z l x x₁ = {!!} -- refLemTraExt'aux₅' j' A B C (node P) (node Q) {!node Z!} l (forcex' x₁ j')
-}

 TraExt'aux₂ : (j  : Size) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2E Z)) 
              → (x₁ : ∞Trx j l (extChPE' (extChNode P Q) Z (inr x))) 
              → ∞Trx j l (extChPE' P (extChNode Q Z) (inr (inr x)))
 forcex' (TraExt'aux₂ j {A} {B} {C} P Q Z l x x₁) j' = LemTraExt'aux₂ j j' P Q Z l x x₁


 LemTraExt'aux₂ : (j  : Size) → (j' : Size< j) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2E Z)) 
              → (x₁ : ∞Trx j l (extChPE' (extChNode P Q) Z (inr x)))
              →  Trx j' l (fmapx' j' (inl ∘ inr) (fmapx' j' (inl ∘ inr) (forcex (node2PE Z x) j')))
 LemTraExt'aux₂ j j' {A} {B} {C}  P Q Z l x x₁ = {!!}  -- refLemTraExt'aux₅' j' A B C (node P) (node Q) {!!} l (forcex' x₁ j')

 TraExt'aux₃ : (j  : Size) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2I {j} {A} P)) 
              → (x₁ : ∞Trx j (l) (extChPI' {j} {(A + B) + (A × B)} {C} (extChNode {j} {A} {B} P Q) Z (inl (inl x)))) 
              → ∞Trx j (l) (extChPI'{j} {A} {(B + C) + (B × C)} P (extChNode {j} {B} {C} Q Z) (inl x))
 forcex' (TraExt'aux₃ j {A} {B} {C} P Q Z l x x₁) j' = {!!}  -- LemTraExt'aux₃ j j' {!P!} Q Z l x (forcex' x₁ j')


 LemTraExt'aux₃ : (j'  : Size) → (j : Size< j') → {A B C : Set} → (P : Node j' A) → (Q : Node j' B) → (Z : Node j' C)
                  → (l  : List Label)
                  → (x  : ChoiceSet (node2I P))
                  → Trx j l (extChx' j (extChx' j (forcex (node2PI P x) j) (node Q)) (node Z))
                  → Trx j l (extChx' j (forcex (node2PI P x) j) (extChx' j (node Q) (node Z)))
 LemTraExt'aux₃ j' j {A} {B} {C} P Q Z l x x₁ = refLemTraExt'aux₅' j A B C (forcex (node2PI P x) j) (node Q) (node Z) l x₁


 TraExt'aux₄ : (j  : Size) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2I Q)) 
              → (x₁ : ∞Trx j l (extChPI' (extChNode P Q) Z (inl (inr x)))) 
              →  ∞Trx j l (extChPI' P (extChNode Q Z) (inr (inl x)))
 forcex' (TraExt'aux₄ j {A} {B} {C} P Q Z l x x₁) j' = LemTraExt'aux₄ j j' P Q Z l x (forcex' x₁ j')

 LemTraExt'aux₄ : (j'  : Size) → (j : Size< j') → {A B C : Set} → (P : Node j' A) → (Q : Node j' B) → (Z : Node j' C)
                  → (l  : List Label)
                  → (x  : ChoiceSet (node2I Q))
                  → Trx j l (extChx' j (extChx' j (node P) (forcex (node2PI Q x) j)) (node Z)) 
                  → Trx j l (extChx' j (node P) (extChx' j (forcex (node2PI Q x) j) (node Z)) ) 
 LemTraExt'aux₄ j' j {A} {B} {C} P Q Z l x x₁ = refLemTraExt'aux₅' j A B C (node P) (forcex (node2PI Q x) j) (node Z) l x₁


 TraExt'aux₅ : (j  : Size) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2I Z)) 
              → (x₁ : ∞Trx j (l) (extChPI' (extChNode P Q) Z (inr x)))
              →  ∞Trx j (l) (extChPI' P (extChNode Q Z) (inr (inr x)))
 forcex' (TraExt'aux₅ j {A} {B} {C} P Q Z l x x₁) j' = let  x₁' : ∞Trx j { (((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C) } l (extChPI' (extChNode {j} P Q) Z (inr x))
                                                            x₁' = x₁ 
                                                            j''  : Size< j
                                                            j''  = j' 

                                                            u : Processx j' ((((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C))
                                                            u = (forcex (extChPI' { j } {(A + B) + (A × B)} { C } 
                                                                     (extChNode { j } { A } { B } P Q) Z (inr x)) j')                                                                                  -- the last argument of the type of x₂

                                                            u' : Processx j' ((((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C))
                                                            u' = (extChx' j' { (A + B) + (A × B) } { C } (extChx' j { A } { B } (node P) (node Q)) (forcex (node2PI {j} Z x) j'))                                                                    -- change j' to j
                                                            -- the last argument of the type of x₃

                                                            uu' : u == u'
                                                            uu' = refl
                                                            -- not equal

                                                            u''' : Processx j' ((A + B) + (A × B))
                                                            u''' = (extChx' j' { A } { B } (node {j'} {A} P) (node {j'} {B} Q))
                                                            -- last argument of u'


                                                            u₄  : Processx j' ((A + B) + (A × B))
                                                            u₄  = node {j' } { (A + B) + (A × B) } 
                                                                    (thenode { j'} {(A + B) + (A × B)} (node2E {j} {A} P +' node2E {j} {B} Q) 
                                                                             (extChLab' {j'} {A} {B} P Q) (extChPE' {j'} {A} {B} P Q)
                                                                     (node2I {j} {A} P +' node2I {j} {B} Q) (extChPI' {j'} {A} {B} P Q))
                                                            -- normal form of u''' which is last argument of u'

                                                            u'''u₄ : u''' == u₄
                                                            u'''u₄ = refl


                                                            u'' : Processx j' ((((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C))
                                                            u'' = extChx' j' { (A + B) + (A × B) } { C } 
                                                                    (node {j'} {(A + B) + (A × B)}
                                                                     (thenode (node2E { j } {A} P +' node2E { j } {B} Q) 
                                                                              (extChLab' {j} {A} {B } P Q) (extChPE' {j'} {A} {B} P Q)
                                                                      (node2I {j} {A} P +' node2I {j} {B} Q) (extChPI' {j'} {A} {B} P Q)))
                                                                    (forcex (node2PI {j} {C} Z x) j')                 
                                                            -- u' with last arguent replaced by normal form u₄
             -- normal form of 
             -- (forcex (extChPI' { j } {(A + B) + (A × B)} (extChNode P Q) Z (inr x)) j') 
                                                            
                                                            x₂  : Trx j' { (((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C) }  l 
                                                                      (forcex (extChPI' {j} {(A + B) + (A × B)} {C} (extChNode {j} {A} {B}  P Q) Z (inr x)) j')
                                                            x₂  = forcex' x₁ j'

                                                            x₃ : Trx j' { (((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C) } l 
                                                                 (extChx' j' { (A + B) + (A × B) } { C } (extChx' j' { A } { B } (node P) (node Q)) (forcex (node2PI Z x) j')) 
--                                                                      (forcex (extChPI' (extChNode P Q) Z (inr x)) j')

                                                            x₃ = {!!} -- (forcex (node2PI Z x) j')
                                                            -- setting goal to x₂ doesn't workx
                                                            -- j != j' of type Size
                                                            -- when checking that the expression x₂ has type
                                                            -- Trx j' l
                                                            -- (extChx' j' (extChx' j' (node P) (node Q))
                                                           --  (forcex (node2PI Z x) j'))
                                                          
                                             
                                                       in LemTraExt'aux₅ j j' P Q Z l x x₃  -- (forcex' x₁ {!j'!})

-- normal form of (extChx' j' (extChx' j' (node P) (node Q)) (forcex (node2PI Z x) j'))
-- is  extChx' j' (node  (thenode (node2E P +' node2E Q) (extChLab' P Q) (extChPE' P Q)   (node2I P +' node2I Q) (extChPI' P Q))) 
--            (forcex (node2PI Z x) j')
-- normal form of (forcex (extChPI' (extChNode P Q) Z (inr x)) j')
-- is  (extChx' j' (extChx' j' (node P) (node Q))  
--            (forcex (node2PI Z x) j'))
-- normal form of (extChx' j' (node P) (node Q)) 
-- is   (node  (thenode (node2E P +' node2E Q) (extChLab' P Q) (extChPE' P Q) (node2I P +' node2I Q) (extChPI' P Q)))
-- normal form of  (forcex (node2PI Z x) j')
-- type of x₁          ∞Trx j l (extChPI' (extChNode P Q) Z (inr x))
-- type of expression     Trx j' l   (extChx' j' (node (extChNode P Q)) (forcex (node2PI Z x) j'))
-- type of goal           Trx j' l   (extChx' j' (node (extChNode P Q)) (forcex (node2PI Z x) j'))

 LemTraExt'aux₅ : (j'  : Size) → (j : Size< j') → {A B C : Set} → (P : Node j' A) → (Q : Node j' B) → (Z : Node j' C)
                  → (l  : List Label)
                  → (x  : ChoiceSet (node2I Z))
                  → Trx j l (extChx' j (extChx' j (node P) (node Q)) (forcex (node2PI Z x) j))
                  → Trx j l (extChx' j (node P) (extChx' j (node Q) (forcex (node2PI Z x) j)))
 LemTraExt'aux₅ j' j {A} {B} {C} P Q Z l x x₁ = refLemTraExt'aux₅' j A B C (node P) (node Q) (forcex (node2PI Z x) j) l x₁



 refLemTraExt'aux₅' : (j  : Size)  → (A  B C : Set) → (P : Processx j A) → (Q  : Processx j B) → (Z : Processx j C)
                    → (l  : List Label) 
                    → ( Trx j l (extChx' j (extChx' j P Q) Z))
                    →   Trx j l (extChx' j P (extChx' j Q Z)) 

 refLemTraExt'aux₅' j A B C (node x) (node x₁) (node x₂) .[] empty = empty
 refLemTraExt'aux₅' j A B C (node x) (node x₁) (node x₂) .(node2Lab x x₃ :: l) (extchoice (inl (inl x₃)) l x₄) = extchoice (inl x₃) l (TraExt'aux j x x₁ x₂ l x₃ x₄)
 refLemTraExt'aux₅' j A B C (node x) (node x₁) (node x₂) .(node2Lab x₁ x₃ :: l) (extchoice (inl (inr x₃)) l x₄) = extchoice (inr (inl x₃)) l (TraExt'aux₁ j x x₁ x₂ l x₃ x₄)
 refLemTraExt'aux₅' j A B C (node x) (node x₁) (node x₂) .(node2Lab x₂ x₃ :: l) (extchoice (inr x₃) l x₄) = extchoice (inr (inr x₃)) l (TraExt'aux₂ j x x₁ x₂ l x₃ x₄)
 refLemTraExt'aux₅' j A B C (node x) (node x₁) (node x₂) .(l :: ll) (intchoice (inl (inl x₃)) l ll x₄) = intchoice (inl x₃) l ll (TraExt'aux₃ j x x₁ x₂ (l :: ll) x₃ x₄)
 refLemTraExt'aux₅' j A B C (node x) (node x₁) (node x₂) .(l :: ll) (intchoice (inl (inr x₃)) l ll x₄) = intchoice (inr (inl x₃)) l ll (TraExt'aux₄ j x x₁ x₂ (l :: ll) x₃ x₄)
 refLemTraExt'aux₅' j A B C (node x) (node x₁) (node x₂) .(l :: ll) (intchoice (inr x₃) l ll x₄) = intchoice (inr (inr x₃)) l ll (TraExt'aux₅ j x x₁ x₂ (l :: ll) x₃ x₄)
 refLemTraExt'aux₅' j A B C (node x) (node x₁) (terminate x₂) .[] empty = empty
 refLemTraExt'aux₅' j A B C (node (thenode E Lab PE I PI)) (terminate x₁) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .[] empty = empty
 refLemTraExt'aux₅' j A B C (node (thenode E Lab PE I PI)) (terminate x₁) (terminate x₂) .[] empty = empty
 refLemTraExt'aux₅' j A B C (terminate x) (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .[] empty = empty
 refLemTraExt'aux₅' j A B C (terminate x) (node (thenode E Lab PE I PI)) (terminate x₂) .[] empty = empty
 refLemTraExt'aux₅' j A B C (terminate x) (terminate x₁) (node (thenode E Lab PE I PI)) .[] empty = empty
 refLemTraExt'aux₅' j A B C (terminate x) (terminate x₁) (terminate x₂) .[] empty = empty
 


{-
not 3 -- (inl (inl x))  → in    (inl x) → out
Goal: ∞Trx j (l₁ :: l) (extChPI' P (extChNode Q Z) (inl x))
————————————————————————————————————————————————————————————
x₁ : ∞Trx j (l₁ :: l) (extChPI' (extChNode P Q) Z (inl (inl x)))
x  : ChoiceSet (node2I P)

Ok 4 -- (inl (inr x)) --> in   (inr (inl x)) → out
Goal: ∞Trx j (l₁ :: l) (extChPI' P (extChNode Q Z) (inr (inl x)))
————————————————————————————————————————————————————————————
x₁ : ∞Trx j (l₁ :: l) (extChPI' (extChNode P Q) Z (inl (inr x)))
x  : ChoiceSet (node2I Q)

————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————
not 5 -- (inr x)  --> in    (inr (inr x)) → out
Goal: ∞Trx j (l₁ :: l) (extChPI' P (extChNode Q Z) (inr (inr x)))
————————————————————————————————————————————————————————————
x₁ : ∞Trx j (l₁ :: l) (extChPI' (extChNode P Q) Z (inr x))
x  : ChoiceSet (node2I Z)
-}



{-
      (j : Size) (A B C : Set) (P : Processx j A)(Q : Processx j B) (Z : Processx j C) (l : List Label) →
      Trx j {(((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C)} l (extChx' j {(A + B) + (A × B)} {C} (extChx' j {A} {B} P Q) Z) →
      Trx j {(A + ((B + C) + (B × C))) + (A × ((B + C) + (B × C)))} l (extChx' j {A} {(B + C) + (B × C)} P (extChx' j {B} {C} Q Z))
-}
{-
————————————————————————————————————————————————————————————————————————————————————————————————————————————————————————
not 5 -- (inr x)  --> in    (inr (inr x)) → out
Goal: ∞Trx j (l₁ :: l) (extChPI' P (extChNode Q Z) (inr (inr x)))
————————————————————————————————————————————————————————————
x₁ : ∞Trx j (l₁ :: l) (extChPI' (extChNode P Q) Z (inr x))
x  : ChoiceSet (node2I Z)
-}




mutual
 UnitExt : (i : Size) → {A B : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) 
            → ( Q) ⊑ (Stop' ⊤'  □ Q) 

 forcex' (UnitExt i P Q l x) j  =  UnitExt' j (∞Stop ⊤') (forcex Q j) l (forcex' x j) 

 UnitExt' : (j : Size) → {A B : Set} → (P : Processx j A) →  (Q : Processx j B) 
            → (Q) ⊑' (∞Stop ⊤' □' Q) 


 UnitExt' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .[] empty = empty
 UnitExt' j (node (thenode E Lab PE I PI)) (terminate x₁) .[] empty = empty
 UnitExt' j (terminate x) (node (thenode E Lab PE I PI)) .[] empty = empty
 UnitExt' j (terminate x) (terminate x₁) .[] empty = empty

















{-

--                   (delayTrx f) 
         where 
            x₂  : (j₁ : Size< j) →
                    Trx j₁ l
                    (forcex
                     (node2PE
                      (thenode (extChE' (extChNode P Q) Z) (extChLab' (extChNode P Q) Z)
                       (extChPE' (extChNode P Q) Z) (extChI' (extChNode P Q) Z)
                       (extChPI' (extChNode P Q) Z))
                      (inl (inl x)))
                     j₁)
            x₂ = forcex' x₁

            f : (j₁ : Size< j) →
                  Trx j₁ l
                  (forcex (node2PE (extChNode P (extChNode Q Z)) (inl x)) j₁)
            f j₁ = {!x₂!}


mutual
 TraExt : (i : Size) → {A B C : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) → (Z : ∞Processx i C)
            → (P □ (Q □ Z)) ⊑ ((P □ Q) □ Z) 

 forcex' ( TraExt i P Q Z l x) j  =  TraExt' j (forcex P j) (forcex Q j) (forcex Z j) l (forcex' x j) 

 TraExt' : (j : Size) → {A B C : Set} → (P : Processx j A) →  (Q : Processx j B)  → (Z : Processx j C)
             → (P □' (Q □' Z)) ⊑' ((P □' Q) □' Z) 

 TraExt' j P Q Z [] empty = empty
 TraExt' j (node P) (node Q) (node Z) (.(node2Lab P x) :: l) (extchoice (inl (inl x)) .l x₁) 
      =   extchoice (inl x) l 
                    (lemmaTrx j l 
                        (node2PE (thenode (extChE' (extChNode P Q) Z) 
                                          (extChLab' (extChNode P Q) Z) 
                                          (extChPE' (extChNode P Q) Z) 
                                          (extChI' (extChNode P Q) Z)(extChPI' (extChNode P Q) Z))(inl (inl x))) 
                        (node2PE (extChNode P (extChNode Q Z)) 
                        (inl x)) 
                        {!x₁!} 
                        x₁) 
 TraExt' j (node P) (node Q) (node Z) (.(node2Lab Q x) :: l) (extchoice (inl (inr x)) .l x₁) = extchoice (inr (inl x)) l (lemmaTrx j l (node2PE (thenode (extChE' (extChNode P Q) Z) (extChLab' (extChNode P Q) Z) (extChPE' (extChNode P Q) Z) (extChI' (extChNode P Q) Z) (extChPI' (extChNode P Q) Z)) (inl (inr x))) (node2PE (extChNode P (extChNode Q Z)) (inr (inl x))) {!!} x₁)
 TraExt' j (node P) (node Q) (node Z) (.(node2Lab Z x) :: l) (extchoice (inr x) .l x₁) = extchoice (inr (inr x)) l (lemmaTrx j l (node2PE(thenode (extChE' (extChNode P Q) Z) (extChLab' (extChNode P Q) Z)(extChPE' (extChNode P Q) Z) (extChI' (extChNode P Q) Z)(extChPI' (extChNode P Q) Z))(inr x)) (node2PE (extChNode P (extChNode Q Z)) (inr (inr x))) {!!} x₁)
 TraExt' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) (node (thenode E₂ Lab₂ PE₂ I₂ PI₂)) (l₁ :: l) (intchoice (inl (inl x)) .l₁ .l x₁) = intchoice (inl x) l₁ l (lemmaTrx j (l₁ :: l) (node2PI (thenode (extChE' (extChNode (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁)) (thenode E₂ Lab₂ PE₂ I₂ PI₂)) (extChLab' (extChNode (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁))(thenode E₂ Lab₂ PE₂ I₂ PI₂))(extChPE' (extChNode (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁)) (thenode E₂ Lab₂ PE₂ I₂ PI₂))(extChI' (extChNode (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁))(thenode E₂ Lab₂ PE₂ I₂ PI₂))(extChPI' (extChNode (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁))(thenode E₂ Lab₂ PE₂ I₂ PI₂)))(inl (inl x))) (node2PI (extChNode (thenode E Lab PE I PI)(extChNode (thenode E₁ Lab₁ PE₁ I₁ PI₁)(thenode E₂ Lab₂ PE₂ I₂ PI₂)))(inl x)) {!!} x₁)
 TraExt' j (node P) (node Q) (node Z) (l₁ :: l) (intchoice (inl (inr x)) .l₁ .l x₁) = intchoice (inr (inl x)) l₁ l (lemmaTrx j (l₁ :: l) (node2PI (thenode (extChE' (extChNode P Q) Z) (extChLab' (extChNode P Q) Z) (extChPE' (extChNode P Q) Z) (extChI' (extChNode P Q) Z) (extChPI' (extChNode P Q) Z))(inl (inr x))) (node2PI (extChNode P (extChNode Q Z)) (inr (inl x))) {!!} x₁)
 TraExt' j (node P) (node Q) (node Z) (l₁ :: l) (intchoice (inr x) .l₁ .l x₁) = intchoice (inr (inr x)) l₁ l (lemmaTrx j (l₁ :: l) (node2PI (thenode (extChE' (extChNode P Q) Z) (extChLab' (extChNode P Q) Z)(extChPE' (extChNode P Q) Z) (extChI' (extChNode P Q) Z)(extChPI' (extChNode P Q) Z))(inr x)) (node2PI (extChNode P (extChNode Q Z)) (inr (inr x))) {!!} x₁)
 TraExt' j (node P) (node Q) (terminate Z) (a :: l) ()
 TraExt' j (node (thenode E Lab PE I PI)) (terminate Q) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) (a :: l) ()
 TraExt' j (node (thenode E Lab PE I PI)) (terminate Q) (terminate Z) (a :: l) ()
 TraExt' j (terminate P) (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) (a :: l) ()
 TraExt' j (terminate P) (node (thenode E Lab PE I PI)) (terminate Z) (a :: l) ()
 TraExt' j (terminate P) (terminate Q) (node (thenode E Lab PE I PI)) (a :: l) ()
 TraExt' j (terminate P) (terminate Q) (terminate Z) (a :: l) ()
-}




{-
mutual
 UnitExt : (i : Size) → {A B : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) 
            → (Stop' ⊤'  □ Q) ⊑ (Q) 

 forcex' (UnitExt i P Q l x) j  =  UnitExt' j (∞Stop ⊤') (forcex Q j) l (forcex' x j) 

 UnitExt' : (j : Size) → {A B : Set} → (P : Processx j A) →  (Q : Processx j B) 
            → (∞Stop ⊤' □' Q) ⊑' (Q) 


 UnitExt' j (node x) (node x₁) .[] empty = empty
 UnitExt' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(Lab₁ x₁ :: l) (extchoice x₁ l x₂) = {!!}
 UnitExt' j (node x) (node (thenode E Lab PE I PI)) .(l :: ll) (intchoice x₁ l ll x₂) = {!!}
 UnitExt' j (node x) (terminate x₁) .[] empty = empty
 UnitExt' j (terminate x) (node x₁) .[] empty = empty
 UnitExt' j (terminate x) (node (thenode E Lab PE I PI)) .(Lab x₁ :: l) (extchoice x₁ l x₂) = {!!}
 UnitExt' j (terminate x) (node (thenode E Lab PE I PI)) .(l :: ll) (intchoice x₁ l ll x₂) = {!!}
 UnitExt' j (terminate x) (terminate x₁) .[] empty = empty
-}




{-

            x₂  : (j₁ : Size< j) →
                    Trx j₁ l
                    (forcex
                     (node2PE
                      (thenode (extChE' (extChNode P Q) Z) (extChLab' (extChNode P Q) Z)
                       (extChPE' (extChNode P Q) Z) (extChI' (extChNode P Q) Z)
                       (extChPI' (extChNode P Q) Z))
                      (inl (inl x)))
                     j₁)
            x₂  = forcex' x₁



                    (lemmaTrx j l 
                        (node2PE (thenode (extChE'   (extChNode P Q) Z) 
                                          (extChLab' (extChNode P Q) Z) 
                                          (extChPE'  (extChNode P Q) Z) 
                                          (extChI'   (extChNode P Q) Z)
                                          (extChPI'  (extChNode P Q) Z)) (inl (inl x))) 
                        (node2PE (extChNode P (extChNode Q Z)) 
                        (inl x)) 
                        {!x₁!} 
                        x₁) -}


















{-
      (j : Size) (A B C : Set) (P : Processx j A)(Q : Processx j B) (Z : Processx j C) (l : List Label) →
      Trx j {(((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C)} l (extChx' j {(A + B) + (A × B)} {C} (extChx' j {A} {B} P Q) Z) →
      Trx j {(A + ((B + C) + (B × C))) + (A × ((B + C) + (B × C)))} l (extChx' j {A} {(B + C) + (B × C)} P (extChx' j {B} {C} Q Z))
-}

{-
 refExtChoice : (i : Size) → {A B : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) 
            → Refinementx i {(A + B) + (A × B)} {(B + A) + (B × A)} (extChx i P Q) (extChx i Q P) 

 forcex' ( refExtChoice i P Q l x) j  =  refExtChoice' j (forcex P j) (forcex Q j) l (forcex' x j) 

 refExtChoice' : (j : Size) → {A B : Set} → (P : Processx j A) →  (Q : Processx j B) 
            → Refinementx' j {(A + B) + (A × B)} {(B + A) + (B × A)} (extChx' j P Q) (extChx' j Q P) 

-}
-- {(((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C)}{(A + ((A + ((B + C) + (B × C))) + (A × ((B + C) + (B × C))))) + (A × ((A + ((B + C) + (B × C))) + (A × ((B + C) + (B × C)))))}

mutual
 TraExtChoice : (i : Size) → {A B C : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) →  (Z : ∞Processx i C) 
            → Refinementx i {(((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C)} {(A + ((B + C) + (B × C))) + (A × ((B + C) + (B × C)))}  (extChx i (extChx i P Q) Z) (extChx i P (extChx i Q Z)) 

 forcex' ( TraExtChoice i P Q Z l x) j  =  TraExtChoice' j (forcex P j) (forcex Q j) (forcex Z j) l  (forcex' x j) 

 TraExtChoice' : (j : Size) → {A B C : Set} → (P : Processx j A) →  (Q : Processx j B) →  (Z : Processx j C) 
            → Refinementx' j (extChx' j (extChx' j P Q) Z) (extChx' j P (extChx' j Q Z)) 


 TraExtChoice' j (node P) (node Q) (node Z) .[] empty = empty
 TraExtChoice' j (node P) (node Q) (node Z) .(node2Lab P x :: l) (extchoice (inl x) l x₁) = extchoice (inl (inl x)) l (lemₑ j P Q Z l x x₁)
 TraExtChoice' j (node P) (node Q) (node Z) .(node2Lab Q x :: l) (extchoice (inr (inl x)) l x₁) = {!!}
 TraExtChoice' j (node P) (node Q) (node Z) .(node2Lab Z x :: l) (extchoice (inr (inr x)) l x₁) = {!!}
 TraExtChoice' j (node P) (node Q) (node Z) .(l :: ll) (intchoice (inl x) l ll x₁) = intchoice (inl (inl x)) l ll {!!}
 TraExtChoice' j (node P) (node Q) (node Z) .(l :: ll) (intchoice (inr (inl x)) l ll x₁) = {!!}
 TraExtChoice' j (node P) (node Q) (node Z) .(l :: ll) (intchoice (inr (inr x)) l ll x₁) = {!!}
 TraExtChoice' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) (terminate Z) .[] empty = empty
 TraExtChoice' j (node (thenode E Lab PE I PI)) (terminate x₁) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .[] empty = empty
 TraExtChoice' j (node (thenode E Lab PE I PI)) (terminate Q) (terminate Z) .[] empty = empty
 TraExtChoice' j (terminate P) (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .[] empty = empty
 TraExtChoice' j (terminate P) (node (thenode E Lab PE I PI)) (terminate Z) .[] empty = empty
 TraExtChoice' j (terminate P) (terminate Q) (node (thenode E Lab PE I PI)) .[] empty = empty
 TraExtChoice' j (terminate P) (terminate Q) (terminate Z) .[] empty = empty



{-
Goal: ∞Trx j l (extChPE' (extChNode P Q) Z (inl (inl x)))
————————————————————————————————————————————————————————————
x₁ : ∞Trx j l (extChPE' P (extChNode Q Z) (inl x))
l  : List Label
x  : ChoiceSet (node2E P)
Z  : Node j .C
Q  : Node j .B
P  : Node j .A
.C : Set
.B : Set
.A : Set
j  : Size

 lemₑ₁ 


TraExt'aux : (j  : Size) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2E P)) 
              → (x₁ : ∞Trx j l (extChPE' (extChNode P Q) Z (inl (inl x)))) 
              → ∞Trx j l (extChPE' P (extChNode Q Z) (inl x))
 forcex' (TraExt'aux j {A} {B} {C}  P Q Z l x x₁) j' = {!!}

LemTraExt'aux : (j  : Size) → (j' : Size< j) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2E P)) 
              → (x₁ : ∞Trx j l (extChPE' (extChNode P Q) Z (inl (inl x)))) 
              →  Trx j' l (fmapx' j' (inl ∘ inl) (forcex (node2PE P x) j'))
 LemTraExt'aux j j' {A} {B} {C}  P Q Z l x x₁ = {!!} -- refLemTraExt'aux₅' j' A B C {!(forcex (node2PE P x) j')!} (node Q) (node Z) l (forcex' x₁ j')


-}

 lemₑ  : (j  : Size) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2E P)) 
              → (x₁ : ∞Trx j l (extChPE' P (extChNode Q Z) (inl x))) 
              → ∞Trx j l (extChPE' (extChNode P Q) Z (inl (inl x)))
 forcex' (lemₑ j {A} {B} {C}  P Q Z l x x₁) j' = {!!}

-- LemTra j' A B C (forcex (node2PE P x) j) (node Q) (node Z) l (forcex' x₁ j)
-- indepFmap j' ((A + B) + (A × B)) {!!} ((((A + B) + (A × B)) + C) + (((A + B) + (A × B)) × C)) {!!} (inl ∘ inl) l (fmapx' j' (inl ∘ inl) (forcex (node2PE P x) j')) {!(forcex' x₁ j')!}
-- indepFmap j' B  ((B + A) + (B × A)) ((A + B) + (A × B)) (inl ∘ inl) (inl ∘ inr) l (forcex (node2PE Q x) j') (forcex' tr j')
-- Lemₑ₁ j j' P Q Z l x x₁
{-
 Lemₑ₁ : (j  : Size) → (j' : Size< j) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2E P))
              → (x₁ : ∞Trx j l (extChPE' P (extChNode Q Z) (inl x))) 
              → Trx j' l (fmapx' j' (inl ∘ inl) (fmapx' j' (inl ∘ inl) (forcex (node2PE P x) j')))
 Lemₑ₁ j j' {A} {B} {C}  P Q Z l x x₁ = {!!}
--
--(forcex (node2PI Z x) j)
-}


 lem₃ₜ : (j  : Size) → {A B C : Set} → (P : Node j A) → (Q : Node j B) → (Z : Node j C) 
              → (l : List Label) → (x  : ChoiceSet (node2I P)) 
              → (x₁ : ∞Trx j l (extChPI' P (extChNode Q Z) (inl x))) 
              →  ∞Trx j l (extChPI' (extChNode P Q) Z (inl (inl x)))
 forcex' (lem₃ₜ j {A} {B} {C} P Q Z l x x₁) j' = {!!} -- lem₃ₜ' j j' P Q Z l x (forcex' x₁ j')



 lem₃ₜ' : (j'  : Size)  → (j : Size< j') → {A  B C : Set} → (P  : Node j' A) → (Q  : Node j' B)  → (Z  : Node j' C)
                    → (l  : List Label)
                    → (x : ChoiceSet (node2I P))
                    → (tr :  Trx j l  (extChx' j (forcex (node2PI P x) j) (extChx' j (node Q) (node Z)))) 
                    → Trx j l (extChx' j (extChx' j (forcex (node2PI P x) j) (node Q)) (node Z))
 lem₃ₜ' j j' {A} {B} {C} P Q Z l x tr = LemTra j' A B C (forcex (node2PI P x) j') (node Q) (node Z) l tr


 LemTra : (j  : Size)  → (A  B C : Set) → (P : Processx j A) → (Q  : Processx j B) → (Z : Processx j C)
                    → (l  : List Label) 
                    →   Trx j l  (extChx' j P (extChx' j Q Z))
                    → ( Trx j l (extChx' j (extChx' j P Q) Z)) 

 LemTra j A B C (node x) (node x₁) (node x₂) .[] empty = empty
 LemTra j A B C (node x) (node x₁) (node x₂) .(node2Lab x x₃ :: l) (extchoice (inl x₃) l x₄) = extchoice (inl (inl x₃)) l (lemₑ j x x₁ x₂ l x₃ x₄)
 LemTra j A B C (node x) (node x₁) (node x₂) .(extChLab' x₁ x₂ x₃ :: l) (extchoice (inr x₃) l x₄) = {!!}
 LemTra j A B C (node x) (node x₁) (node x₂) .(l :: ll) (intchoice (inl x₃) l ll x₄) = intchoice (inl (inl x₃)) l ll (lem₃ₜ j x x₁ x₂ (l :: ll) x₃ x₄)
 LemTra j A B C (node x) (node x₁) (node x₂) .(l :: ll) (intchoice (inr x₃) l ll x₄) = {!!}
 LemTra j A B C (node x) (node x₁) (terminate x₂) l tr = {!!}
 LemTra j A B C (node x) (terminate x₁) Z l tr = {!!}
 LemTra j A B C (terminate x) Q Z l tr = {!!}
