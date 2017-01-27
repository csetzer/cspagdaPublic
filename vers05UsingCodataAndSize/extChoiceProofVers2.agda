{-# OPTIONS --copatterns #-}

module extChoiceProofVers2 where
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




mutual
 TraExt : (i : Size) → {A B C : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) → (Z : ∞Processx i C)
            → (P □ (Q □ Z)) ⊑ ((P □ Q) □ Z) 

 forcex' ( TraExt i P Q Z l x) j  =  TraExt' j (forcex P j) (forcex Q j) (forcex Z j) l (forcex' x j) 

 TraExt' : (j : Size) → {A B C : Set} → (P : Processx j A) →  (Q : Processx j B)  → (Z : Processx j C)
             → (P □' (Q □' Z)) ⊑' ((P □' Q) □' Z) 

 TraExt' j P Q Z [] empty = empty
 TraExt' j (node P) (node Q) (node Z) (.(node2Lab P x) :: l) (extchoice (inl (inl x)) .l x₁)   =  extchoice (inl x) l {!TraExtaux' j P Q Z l x₁!}

 TraExtaux' : ∀ {j A B C} {P : Node j A} {x : ChoiceSet (node2E P)}
               j₁ (P₁ : Node j₁ A) (Q : Node j₁ B) (Z : Node j₁ C) l
               (x₁
                : ∞Trx j₁ l
                  (extChPE'
                   (thenode (node2E P₁ +' node2E Q) (extChLab' P₁ Q) (extChPE' P₁ Q)
                    (node2I P₁ +' node2I Q) (extChPI' P₁ Q))
                   Z (inl (inl x)))) →
             ∞Trx j₁ l
             (extChPE' P₁
              (thenode (node2E Q +' node2E Z) (extChLab' Q Z) (extChPE' Q Z)
               (node2I Q +' node2I Z) (extChPI' Q Z))
              (inl x))
 TraExtaux' = ?

 {-        where 
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

            f : (j₁ : Size< j) →
                  Trx j₁ l
                  (forcex (node2PE (extChNode P (extChNode Q Z)) (inl x)) j₁)
            f j₁ = {!!}

-}


{-                    (lemmaTrx j l 
                        (node2PE (thenode (extChE' (extChNode P Q) Z) 
                                          (extChLab' (extChNode P Q) Z) 
                                          (extChPE' (extChNode P Q) Z) 
                                          (extChI' (extChNode P Q) Z)(extChPI' (extChNode P Q) Z))(inl (inl x))) 
                        (node2PE (extChNode P (extChNode Q Z)) 
                        (inl x)) 
                        {!x₁!} 
                        x₁) -}
{- 
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
