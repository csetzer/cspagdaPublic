module proofAssExt where 

open import process
open import Size
open import choiceSetU
open import auxData
open import Data.Maybe
open import Data.List
open import Data.Sum
open import Data.Fin
open import label
open import renamingResult
open import RefWithoutSize
open import dataAuxFunction
open import lemFmap
open import externalChoice
open import addTick
open import internalChoice
open import traceEquivalence
open import Data.Product
open import TraceWithoutSize
open Tr∞

maybeExtC : {c₀ c₁ c₂ : Choice} → Set
maybeExtC {c₀} {c₁} {c₂} = ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂)


mutual 
 A□+ : {c₀ c₁ c₂ : Choice}  (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁) (Z : Process+ ∞ c₂)
        →  ((P □++ Q) □++ Z) ⊑+ fmap+ Ass⊎ᵣ (P □++ (Q  □++ Z ))
 A□+ P Q Z .[] .nothing empty = empty
 A□+ P Q Z .(Lab P x ∷ l) m (extc l .m (inj₁ x) x₁) = let
                                                       x' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x)))
                                                       x' = x₁

                                                       x₁' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₁) ((PE P x)))
                                                       x₁' = lemFmap∞ inj₁ Ass⊎ᵣ (PE P x) l m x'

                                                       x₂' :  Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₁ (PE P x)))
                                                       x₂' = lemFmap∞R inj₁ inj₁ (PE P x) l m x₁'
                                                       
                                                      in extc l m (inj₁ (inj₁ x)) x₂'
                                                      
 A□+ P Q Z .(Lab Q x ∷ l) m (extc l .m (inj₂ (inj₁ x)) x₁) = let
                                                               x₁'' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₁ (PE Q x))))
                                                               x₁'' = x₁

                                                               x₁'  : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₁ (PE Q x)))
                                                               x₁'  = lemFmap∞ inj₂ Ass⊎ᵣ (fmap∞ inj₁ (PE Q x)) l m x₁''

                                                               x₂'  : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₁) (PE Q x))
                                                               x₂'  = lemFmap∞ inj₁ (Ass⊎ᵣ ∘ inj₂) (PE Q x) l m x₁'

                                                               x₃'  : Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₂ (PE Q x)))
                                                               x₃'  = lemFmap∞R inj₂ inj₁ (PE Q x) l m x₂'                                                                                                         

                                                             in extc l m (inj₁ (inj₂ x)) x₃'
                                                             

 A□+ P Q Z .(Lab Z y ∷ l) m (extc l .m (inj₂ (inj₂ y)) x₁) = extc
                    l m (inj₂ y) (lemFmap∞ inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z y) l m (lemFmap∞ inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z y)) l m x₁))
 A□+ P Q Z l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₁ (inj₁ x)) (A□∞++ (PI P x) Q Z l m x₁)
 A□+ P Q Z l m (intc .l .m (inj₂ (inj₁ x)) x₁) = intc l m (inj₁ (inj₂ x)) (A□+∞+ P (PI Q x) Z l m x₁)
 A□+ P Q Z l m (intc .l .m (inj₂ (inj₂ y)) x₁) = intc l m (inj₂ y) (A□++∞ P Q (PI Z y) l m x₁)
 A□+ P Q Z .[] .(just (inj₁ (inj₁ (PT P x)))) (terc (inj₁ x)) = terc (inj₁ (inj₁ x))
 A□+ P Q Z .[] .(just (inj₁ (inj₂ (PT Q x)))) (terc (inj₂ (inj₁ x))) = terc (inj₁ (inj₂ x))
 A□+ P Q Z .[] .(just (inj₂ (PT Z y))) (terc (inj₂ (inj₂ y))) = terc (inj₂ y)


 A□∞++ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                            (Q : Process+ ∞ c₁)
                            (Z : Process+ ∞ c₂)
         → Ref∞  (((P □∞++ Q) □∞++ Z)) (fmap∞ Ass⊎ᵣ ( P □∞++ (Q □++ Z)))
 forcet (A□∞++ P Q Z l m x) =  tnode (A□+pp (forcep P) Q Z l m (forcet' l m (forcet x)))



 A□+∞+ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                            (Q : Process∞ ∞ c₁)
                            (Z : Process+ ∞ c₂)
         → Ref∞ (((P □+∞+ Q) □∞++ Z)) (fmap∞ Ass⊎ᵣ ( P □+∞+ (Q □∞++ Z)))
 forcet (A□+∞+ P Q Z l m x) = tnode (A□p+p P (forcep Q) Z l m (forcet' l m (forcet x)))


 A□++∞  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                             (Q : Process+ ∞ c₁)
                             (Z : Process∞ ∞ c₂)
         → Ref∞ (((P □++ Q) □+∞+ Z)) (fmap∞ Ass⊎ᵣ ( P □+∞+ (Q □+∞+ Z)))
 forcet (A□++∞ P Q Z l m x)  = tnode (A□pp+ P Q (forcep Z) l m (forcet' l m (forcet x)))


 A□+pp  : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                             (Q : Process+ ∞ c₁)
                             (Z : Process+ ∞ c₂)
         →  Ref+ (((P □p++ Q) □++ Z)) (fmap+ Ass⊎ᵣ ( P □p++ (Q □++ Z)))
 A□+pp (terminate x) Q Z l m tr = A□-++ Q Z x l m tr
 A□+pp (node x) Q Z l m tr      = A□+ x Q Z l m tr


 A□p+p : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                            (Q : Process  ∞ c₁)
                            (Z : Process+ ∞ c₂)
         →  Ref+  (((P □+p+ Q) □++ Z)) (fmap+ Ass⊎ᵣ ( P □++ (Q □p++ Z)))
 A□p+p P (terminate x) Z l m tr = A□+-+ P Z x l m tr
 A□p+p P (node x) Z l m tr      = A□+ P x Z l m tr


 A□pp+ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                            (Q : Process+ ∞ c₁)
                            (Z : Process  ∞ c₂)
         →  Ref+ (((P □++ Q) □+p+ Z)) (fmap+ Ass⊎ᵣ ( P □++ (Q □+p+ Z)))
 A□pp+ P Q (terminate x) l m tr = A□++- P Q m l x tr
 A□pp+ P Q (node x) l m tr      = A□+ P Q x  l m tr



 A□++- : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                            (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → ( x : ChoiceSet c₂ )
         → (tr : Tr+ l m (fmap+ Ass⊎ᵣ (P □++ addTimed✓+ (inj₂ x) (fmap+ inj₁ Q))))
         → Tr+ l m (addTimed✓+ (inj₂ x) (fmap+ inj₁ (P □++ Q)))
 A□++- P Q .nothing .[] x empty = empty
 A□++- P Q m .(Lab P x₁ ∷ l) x (extc l .m (inj₁ x₁) x₂) = let
 
                                                           x' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x₁)))
                                                           x' = x₂ 
                                                          
                                                           x₁' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₁) (PE P x₁))
                                                           x₁' = lemFmap∞ inj₁ Ass⊎ᵣ (PE P x₁) l m x'
                                                         
                                                           x₂' :  Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₁ (PE P x₁)))
                                                           x₂' = lemFmap∞R inj₁ inj₁ (PE P x₁) l m x₁'
                                                          
                                                          in  extc l m (inj₁ x₁) x₂'
                                                          
 A□++- P Q m .(Lab Q y ∷ l) x (extc l .m (inj₂ y) x₂) = let
                                                         x' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₁ (PE Q y))))
                                                         x' = x₂
                                                         
                                                         x₁' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₁ (PE Q y)))
                                                         x₁' = lemFmap∞ inj₂ Ass⊎ᵣ (fmap∞ inj₁ (PE Q y)) l m x'
                                                         
                                                         x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₁) (PE Q y))
                                                         x₂' = lemFmap∞ inj₁ (Ass⊎ᵣ ∘ inj₂) (PE Q y) l m x₁'
                                                         
                                                         x₃' :  Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₂ (PE Q y)))
                                                         x₃' = lemFmap∞R inj₂ inj₁ (PE Q y) l m x₂'
                                                         
                                                        in extc l m (inj₂ y) x₃'
                                                        
 A□++- P Q m l x (intc .l .m (inj₁ x₁) x₂)  = intc l m (inj₁ x₁)(A□∞+- (PI P x₁) Q m l x x₂)
 A□++- P Q m l x (intc .l .m (inj₂ y) x₂)   = intc l m (inj₂ y) (A□+∞- P  (PI Q y) m l x x₂)
 A□++- P Q .(just (inj₁ (inj₁ (PT P x₁)))) .[] x (terc (inj₁ x₁))      = terc (inj₂ (inj₁ x₁))
 A□++- P Q .(just (inj₂ x)) .[] x (terc (inj₂ (inj₁ x₁)))              = terc (inj₁ x₁)
 A□++- P Q .(just (inj₁ (inj₂ (PT Q y)))) .[] x (terc (inj₂ (inj₂ y))) = terc (inj₂ (inj₂ y))



 A□-++ : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → (x   : ChoiceSet c₀)
         → (l : List Label)
         → (m : Maybe ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → (tr  : Tr+ l m (fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (Q □++ Z)))))
         →  Tr+ l m (addTimed✓+ (inj₁ x) (fmap+ inj₂ Q) □++ Z)
 A□-++ Q Z x .[] .nothing empty = empty
 A□-++ Q Z x .(Lab Q x₁ ∷ l) m (extc l .m (inj₁ x₁) x₂) = let
 
                                                           x' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₁ (PE Q x₁))))
                                                           x' = x₂
                                                           
                                                           x₁' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₁ (PE Q x₁)))
                                                           x₁' = lemFmap∞ inj₂ Ass⊎ᵣ (fmap∞ inj₁ (PE Q x₁)) l m x'
                                                           
                                                           x₂' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₁) (PE Q x₁)) 
                                                           x₂' = lemFmap∞ inj₁ (Ass⊎ᵣ ∘ inj₂) (PE Q x₁) l m x₁'
                                                           
                                                           x₃' :   Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₂ (PE Q x₁)))
                                                           x₃' = lemFmap∞R inj₂ inj₁ (PE Q x₁) l m x₂'
                                                           
                                                          in extc l m (inj₁ x₁) x₃' 
 A□-++ Q Z x .(Lab Z y ∷ l) m (extc l .m (inj₂ y) x₂) =  let
 
                                                           x' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₂ (PE Z y))))
                                                           x' = x₂ 
                                                           
                                                           x₁' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₂ (PE Z y)))
                                                           x₁' = lemFmap∞ inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z y)) l m x'
                                                           
                                                           x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₂) (PE Z y))
                                                           x₂' = lemFmap∞ inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z y) l m x₁'
                                                          
                                                          in extc l m (inj₂ y) x₂' 
 A□-++ Q Z x l m (intc .l .m (inj₁ x₁) x₂) = intc l m (inj₁ x₁) (A□-∞+ (PI Q x₁) Z x l m x₂)
 A□-++ Q Z x l m (intc .l .m (inj₂ y) x₂) =  intc l m (inj₂ y) (A□-+∞ Q (PI Z y) x l m x₂)
 A□-++ Q Z x .[] .(just (inj₁ (inj₁ x))) (terc (inj₁ x₁)) = terc (inj₁ (inj₁ x₁))
 A□-++ Q Z x .[] .(just (inj₁ (inj₂ (PT Q x₁)))) (terc (inj₂ (inj₁ x₁))) = terc (inj₁ (inj₂ x₁))
 A□-++ Q Z x .[] .(just (inj₂ (PT Z y))) (terc (inj₂ (inj₂ y))) = terc (inj₂ y)



 A□+-+ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → ( tr  : Tr+ l m (fmap+ Ass⊎ᵣ (P □++ addTimed✓+ (inj₁ x) (fmap+ inj₂ Z))))
         →  Tr+ l m (addTimed✓+ (inj₂ x) (fmap+ inj₁ P) □++ Z)
 A□+-+ P Z x .[] .nothing empty = empty
 A□+-+ P Z x .(Lab P x₁ ∷ l) m (extc l .m (inj₁ x₁) x₂) = let
 
                                                           x' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x₁)))
                                                           x' = x₂
                                                           
                                                           x₁' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₁) (PE P x₁))
                                                           x₁' = lemFmap∞ inj₁ Ass⊎ᵣ (PE P x₁) l m x' 
                                                           
                                                           x₂' :  Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₁ (PE P x₁)))
                                                           x₂' = lemFmap∞R inj₁ inj₁ (PE P x₁) l m x₁'
                                                          
                                                          in extc l m (inj₁ x₁) x₂' 
 A□+-+ P Z x .(Lab Z y ∷ l) m (extc l .m (inj₂ y) x₂) =  let
 
                                                           x' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₂ (PE Z y))))
                                                           x' = x₂
                                                           
                                                           x₁' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₂ (PE Z y)))
                                                           x₁' = lemFmap∞ inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z y)) l m x' 
                                                           
                                                           x₂' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₂) (PE Z y))
                                                           x₂' = lemFmap∞ inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z y) l m x₁'
                                                           
                                                          in extc l m (inj₂ y) x₂' 
 A□+-+ P Z x l m (intc .l .m (inj₁ x₁) x₂) = intc l m (inj₁ x₁) (A□∞-+ (PI P x₁) Z x l m x₂)
 A□+-+ P Z x l m (intc .l .m (inj₂ y) x₂) = intc l m (inj₂ y) (A□+-∞ P (PI Z y) x l m x₂)
 A□+-+ P Z x .[] .(just (inj₁ (inj₁ (PT P x₁)))) (terc (inj₁ x₁)) = terc (inj₁ (inj₂ x₁))
 A□+-+ P Z x .[] .(just (inj₁ (inj₂ x))) (terc (inj₂ (inj₁ x₁))) = terc (inj₁ (inj₁ x₁))
 A□+-+ P Z x .[] .(just (inj₂ (PT Z y))) (terc (inj₂ (inj₂ y))) = terc (inj₂ y)



 A□+∞-  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                               (Q : Process∞ ∞ c₁)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂  : Tr∞ l m (fmap∞ Ass⊎ᵣ (P □+∞+ addTimed✓∞ (inj₂ x) (fmap∞ inj₁ (Q )))))
         →  Tr∞ l m (addTimed✓∞ (inj₂ x) (fmap∞ inj₁ (P □+∞+ Q )))
 forcet (A□+∞- P Q m l x x₂) = tnode (A□+p- P (forcep Q) m l x (forcet' l m (forcet x₂))) 


 A□∞+- : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                            (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂  : Tr∞ l m (fmap∞ Ass⊎ᵣ (P □∞++ addTimed✓+ (inj₂ x) (fmap+ inj₁ Q))))
         →  Tr∞ l m (addTimed✓∞ (inj₂ x) (fmap∞ inj₁ (P □∞++ Q)))
 forcet ( A□∞+- P Q m l x x₂) = tnode (A□p+- (forcep P) Q m l x (forcet' l m (forcet x₂)))



 A□-∞+ : {c₀ c₁ c₂ : Choice}(Q : Process∞ ∞ c₁)
                            (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → (x₂ : Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (Q □∞++ Z)))))
         →  Tr∞ l m (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ Q) □∞++ Z)
 forcet (A□-∞+ Q Z x l m tr) = A□-p+ (forcep Q) Z x l m (forcet' l m (forcet tr))

 A□∞-+ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                            (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → ( x₂  : Tr∞ l m (fmap∞ Ass⊎ᵣ (P □∞++ addTimed✓+ (inj₁ x) (fmap+ inj₂ Z))))
         →  Tr∞ l m (addTimed✓∞ (inj₂ x) (fmap∞ inj₁ (P)) □∞++ Z)
 forcet (A□∞-+ P Z x l m x₂) =  A□p-+ (forcep P) Z x l m (forcet' l m (forcet x₂))



 A□+-∞  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                             (Z : Process∞ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  : Tr∞ l m (fmap∞ Ass⊎ᵣ (P □+∞+ addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (Z)))))
         →  Tr∞ l m (addTimed✓+ (inj₂ x) (fmap+ inj₁ P) □+∞+ Z)
 forcet (A□+-∞  P Z x l m x₂) = A□+-p  P (forcep Z) x l m (forcet' l m (forcet x₂))


 A□-+∞  : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                             (Z : Process∞ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  : Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (Q □+∞+ Z)))))
         →  Tr∞ l m (addTimed✓+ (inj₁ x) (fmap+ inj₂ Q) □+∞+ Z )
 forcet (A□-+∞  Q Z x l m tr) = tnode ( A□-+p Q (forcep Z) x l m (forcet' l m (forcet tr)))




 A□p+- : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                              (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂  : Tr+ l m (fmap+ Ass⊎ᵣ (P □p++ addTimed✓+ (inj₂ x) (fmap+ inj₁ Q))))
         →  Tr+ l m ((addTimed✓+ (inj₂ x) (fmap+ inj₁ (P □p++ Q))))
 A□p+- (terminate x) Q m l x₁ x₂ = A□-+- Q x₁ x l m x₂
 A□p+- (node x) Q m l x₁ x₂      = A□++- x Q m l x₁ x₂

 A□+p- : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process  ∞ c₁)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂  : Tr+ l m (fmap+ Ass⊎ᵣ (P □+p+ addTimed✓ (inj₂ x) (fmap inj₁ Q))))
         →  Tr+ l m ((addTimed✓+ (inj₂ x) (fmap+ inj₁ (P □+p+ Q))))
 A□+p- P (terminate x) m l x₁ x₂ =  A□+-- P m l x₁ x (A□+--ₛ P m l x x₁ x₂)
 A□+p- P (node x) m l x₁ x₂      =  A□++- P x m l x₁ x₂ 


 A□+-p  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                             (Z : Process  ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → ( x₂ : Tr+ l m (fmap+ Ass⊎ᵣ (P □+p+ addTimed✓ (inj₁ x) (fmap inj₂ Z))))
         →  Tr l m (node (addTimed✓+ (inj₂ x) (fmap+ inj₁ P) □+p+ Z))
 A□+-p  P (terminate x) x₁ l m x₂ = tnode (A□+-- P m l x x₁ x₂)
 A□+-p  P (node x) x₁ l m x₂      = tnode (A□+-+ P x x₁ l m x₂)


 A□-+p : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                            (Z : Process  ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeExtC) 
         →  (tr  : Tr+ l m ((fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (Q □+p+ Z))))))
         → Tr+ l m ((addTimed✓+ (inj₁ x) (fmap+ inj₂ Q) □+p+ Z))
 A□-+p Q (terminate x) x₁ l m tr = A□-+- Q x x₁ l m tr 
 A□-+p Q (node x) x₁ l m tr      = A□-++ Q x x₁ l m tr

 A□p-+ : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                            (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  : Tr+ l m (fmap+ Ass⊎ᵣ (P □p++ addTimed✓+ (inj₁ x) (fmap+ inj₂ Z))))
         →  Tr l m ( node (addTimed✓ (inj₂ x) (fmap inj₁ P) □p++ Z))
 A□p-+ (terminate x) Z x₁ l m x₂ = A□--+ₛ Z x x₁ l m x₂
 A□p-+ (node x) Z x₁ l m x₂      = tnode (A□+-+ x Z x₁ l m x₂)


 A□-p+ : {c₀ c₁ c₂ : Choice}(Q : Process  ∞ c₁)
                            (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe  ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → (tr  : Tr+ l m (fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (Q □p++ Z)))))
         →  Tr l m (node (addTimed✓ (inj₁ x) (fmap inj₂ Q) □p++ Z))
 A□-p+ (terminate q) Z x l m tr = tnode (A□--+ Z q x l m tr)
 A□-p+ (node q) Z x l m tr      = tnode (A□-++ q Z x l m tr)




 A□-∞- : {c₀ c₁ c₂ : Choice}(Q : Process∞ ∞ c₁)
         → (m  : Maybe  maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₀)
         → (x₁ : ChoiceSet c₂)
         → (x₃ : Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (addTimed✓∞ (inj₂ x₁) (fmap∞ inj₁ (Q)))))))
         →  Tr∞ l m (addTimed✓∞ (inj₂ x₁) (fmap∞ inj₁ (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (Q)))))
 forcet (A□-∞- Q m l x x₁ x₃) =  A□-p- (forcep Q) x₁ x l m (forcet x₃) 

 A□∞-- : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → ( x₃  : Tr∞ l m (fmap∞ Ass⊎ᵣ (P □∞++ fmap+ unifyA⊎A (2-✓+ (inj₁ x₁) (inj₂ x)))))
         →  Tr∞ l m (addTimed✓∞ (inj₂ x) (fmap∞ inj₁ (addTimed✓∞ (inj₂ x₁) (fmap∞ inj₁ ( P)))))
 forcet (A□∞-- P m l x x₁ x₃) = A□p-- (forcep P) x₁ x l m (forcet x₃)


 A□∞--ₛ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → (x₃  : Tr∞ l m (fmap∞ Ass⊎ᵣ  (P □∞++ fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x)))))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (P □∞++ fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ x₁))))
 forcet (A□∞--ₛ P m l x x₁ x₃) =  A□p--ₛ (forcep P) x₁ x l m (forcet x₃)


 A□--∞ₛ : {c₀ c₁ c₂ : Choice}(Z : Process∞ ∞ c₂)
         → (x₁  : ChoiceSet c₁)
         → ( x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₃  : Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (addTimed✓∞ (inj₁ x₁) (fmap∞ inj₂ Z))))))
         →  Tr∞ l m (fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x)) □+∞+ Z)
 forcet (A□--∞ₛ Z q x l m x₂) = A□--pₛ (forcep Z) x q l m (forcet x₂)



 A□--∞ : {c₀ c₁ c₂ : Choice}(Z : Process∞ ∞ c₂)
         → (q  : ChoiceSet c₁)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  : Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (addTimed✓∞ (inj₁ q) (fmap∞ inj₂ Z))))))
         →  Tr∞ l m (fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ q)) □+∞+ Z)
 forcet (A□--∞ Z q x l m x₂) = A□--p (forcep Z) x q l m (forcet x₂)



 A□--p : {c₀ c₁ c₂ : Choice}(Z : Process ∞ c₂)
         → (x : ChoiceSet c₀)
         → (q : ChoiceSet c₁)
         → (l : List Label)
         → (m : Maybe  ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → (x₂ : Tr l m (fmap Ass⊎ᵣ (addTimed✓ (inj₁ x)(fmap inj₂ (addTimed✓ (inj₁ q) (fmap inj₂ Z))))))
         → Tr l m (node (fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ q)) □+p+ Z))
 A□--p (terminate x) x₁ q .[] .nothing (tnode empty) = tnode empty
 A□--p (terminate x) x₁ q .(efq _ ∷ l) m (tnode (extc l .m () x₃))
 A□--p (terminate x) x₁ q l m (tnode (intc .l .m () x₃))
 A□--p (terminate x) x₁ q .[] .(just (inj₁ (inj₁ x₁))) (tnode (terc (inj₁ zero))) = tnode (terc (inj₂ zero))
 A□--p (terminate x) x₁ q .[] .(just (inj₁ (inj₁ x₁))) (tnode (terc (inj₁ (suc ()))))
 A□--p (terminate x) x₁ q .[] .(just (inj₁ (inj₂ q))) (tnode (terc (inj₂ zero))) = tnode (terc (inj₂ (suc zero)))
 A□--p (terminate x) x₁ q .[] .(just (inj₂ x)) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₁ zero))
 A□--p (terminate x) x₁ q .[] .(just (Ass⊎ᵣ (inj₂ (unifyA⊎A (if suc (suc _) then inj₁ (inj₁ q)
                                                               else (inj₂ (inj₂ x))))))) (tnode (terc (inj₂ (suc (suc ()))))) 
 A□--p (node x) x₁ q l m x₂ = tnode (A□--+ x q x₁ l m (forcet' l m x₂))

 A□--pₛ : {c₀ c₁ c₂ : Choice}(Z : Process ∞ c₂)
         → (x : ChoiceSet c₀)
         → (q : ChoiceSet c₁)
         → (l : List Label)
         → (m : Maybe  ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → ( x₂  : Tr l m (fmap Ass⊎ᵣ (addTimed✓ (inj₁ x) (fmap inj₂ (addTimed✓ (inj₁ q) (fmap inj₂ Z))))))
         →  Tr l m  (node (fmap+ unifyA⊎A (2-✓+ (inj₂ q) (inj₁ x)) □+p+ Z))
 A□--pₛ (terminate x) x₁ q .[] .nothing (tnode empty) = tnode empty
 A□--pₛ (terminate x) x₁ q .(efq _ ∷ l) m (tnode (extc l .m () x₃))
 A□--pₛ (terminate x) x₁ q l m (tnode (intc .l .m () x₃))
 A□--pₛ (terminate x) x₁ q .[] .(just (inj₁ (inj₁ x₁))) (tnode (terc (inj₁ zero))) = tnode (terc (inj₂ (suc zero)))
 A□--pₛ (terminate x) x₁ q .[] .(just (inj₁ (inj₁ x₁))) (tnode (terc (inj₁ (suc ()))))
 A□--pₛ (terminate x) x₁ q .[] .(just (inj₁ (inj₂ q))) (tnode (terc (inj₂ zero))) = tnode (terc (inj₂ zero))
 A□--pₛ (terminate x) x₁ q .[] .(just (inj₂ x)) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₁ zero))
 A□--pₛ (terminate x) x₁ q .[] .(just (Ass⊎ᵣ (inj₂ (unifyA⊎A (if suc (suc _) then inj₁ (inj₁ q)
                                                                 else (inj₂ (inj₂ x))))))) (tnode (terc (inj₂ (suc (suc ())))))
 A□--pₛ (node x) x₁ q l m x₂ =  A□--+ₛ x x₁ q l m (forcet' l m x₂)



 A□p-- : {c₀ c₁ c₂ : Choice}(P : Process ∞ c₀)
         → (x₁ : ChoiceSet c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₃  : Tr l m (node (fmap+ Ass⊎ᵣ (P □p++ fmap+ unifyA⊎A (2-✓+ (inj₁ x₁) (inj₂ x))))))
         →  Tr l m (addTimed✓ (inj₂ x) (fmap inj₁ (addTimed✓ (inj₂ x₁) (fmap inj₁ (P)))))
 A□p-- (terminate x) x₁ x₂ .[] .nothing (tnode empty) = tnode empty
 A□p-- (terminate x) x₁ x₂ .(efq _ ∷ l) m (tnode (extc l .m () x₄))
 A□p-- (terminate x) x₁ x₂ l m (tnode (intc .l .m () x₄))
 A□p-- (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₁ x))) (tnode (terc (inj₁ x₃))) = tnode (terc (inj₂ (suc zero)))
 A□p-- (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₂ x₁))) (tnode (terc (inj₂ zero))) = tnode (terc (inj₂ zero))
 A□p-- (terminate x) x₁ x₂ .[] .(just (inj₂ x₂)) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₁ zero))
 A□p-- (terminate x) x₁ x₂ .[] .(just (Ass⊎ᵣ (inj₂ (unifyA⊎A (if suc (suc _) then inj₁ (inj₁ x₁)
                                                                else (inj₂ (inj₂ x₂))))))) (tnode (terc (inj₂ (suc (suc ()))))) 
 A□p-- (node x)      x₁ x₂ l m x₃ = tnode (A□+-- x m l x₂ x₁ (forcet' l m x₃))


 A□p--ₛ : {c₀ c₁ c₂ : Choice}(P : Process ∞ c₀)
         → (x₁ : ChoiceSet c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₃  : Tr l m (node (fmap+ Ass⊎ᵣ (P □p++ fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x))))))
        → Tr l m (node (fmap+ Ass⊎ᵣ (P □p++ fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ x₁)))))
 A□p--ₛ (terminate x) x₁ x₂ .[] .nothing (tnode empty) = tnode empty
 A□p--ₛ (terminate x) x₁ x₂ .(efq _ ∷ l) m (tnode (extc l .m () x₄))
 A□p--ₛ (terminate x) x₁ x₂ l m (tnode (intc .l .m () x₄))
 A□p--ₛ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₁ x))) (tnode (terc (inj₁ zero))) = tnode (terc (inj₁ zero))
 A□p--ₛ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₁ x))) (tnode (terc (inj₁ (suc ()))))
 A□p--ₛ (terminate x) x₁ x₂ .[] .(just (inj₂ x₁)) (tnode (terc (inj₂ zero))) = tnode (terc (inj₂ (suc zero)))
 A□p--ₛ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₂ x₂))) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₂ zero))
 A□p--ₛ (terminate x) x₁ x₂ .[] .(just (Ass⊎ᵣ (inj₂ (unifyA⊎A (if suc (suc _) then inj₁ (inj₂ x₁)
                                                                else (inj₂ (inj₁ x₂))))))) (tnode (terc (inj₂ (suc (suc ())))))
 A□p--ₛ (node x) x₁ x₂ l m (tnode x₃) = tnode (A□+--ₛ x m l x₂ x₁ x₃)

 A□-p- : {c₀ c₁ c₂ : Choice}(Q : Process ∞ c₁)
         → (x₁ : ChoiceSet c₀)
         → (x  : ChoiceSet c₂)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → ( x₃  : Tr l m (fmap Ass⊎ᵣ (addTimed✓ (inj₁ x) (fmap inj₂ (addTimed✓ (inj₂ x₁) (fmap inj₁ Q))))))
         →  Tr l m (addTimed✓ (inj₂ x₁) (fmap inj₁ (addTimed✓ (inj₁ x) (fmap inj₂ ( Q)))))
 A□-p- (terminate x) x₁ x₂ .[] .nothing (tnode empty) = tnode empty
 A□-p- (terminate x) x₁ x₂ .(efq _ ∷ l) m (tnode (extc l .m () x₄))
 A□-p- (terminate x) x₁ x₂ l m (tnode (intc .l .m () x₄))
 A□-p- (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₁ x₂))) (tnode (terc (inj₁ zero))) = tnode (terc (inj₂ zero))
 A□-p- (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₁ x₂))) (tnode (terc (inj₁ (suc ()))))
 A□-p- (terminate x) x₁ x₂ .[] .(just (inj₂ x₁)) (tnode (terc (inj₂ zero))) = tnode (terc (inj₁ zero))
 A□-p- (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₂ x))) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₂ (suc zero)))
 A□-p- (terminate x) x₁ x₂ .[] .(just (Ass⊎ᵣ (inj₂ (unifyA⊎A (if suc (suc _) then inj₁ (inj₂ x₁)
                                                                else (inj₂ (inj₁ x))))))) (tnode (terc (inj₂ (suc (suc ())))))
 A□-p- (node x)      x₁ x₂ l m x₃ = tnode (A□-+- x x₁ x₂ l m (forcet' l m x₃)) 


 A□-+- : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
         → (x₁ : ChoiceSet c₀)
         → (x  : ChoiceSet c₂)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → ( x₂  : Tr+ l m (fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (addTimed✓+ (inj₂ x₁) (fmap+ inj₁ Q))))))
         →  Tr+ l m (addTimed✓+ (inj₂ x₁) (fmap+ inj₁ (addTimed✓+ (inj₁ x) (fmap+ inj₂ Q))))
 A□-+- Q x₁ x .[] .nothing empty = empty
 A□-+- Q x₁ x .(Lab Q x₂ ∷ l) m (extc l .m x₂ x₃) = let
                                                     x' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₁ (PE Q x₂))))
                                                     x' = x₃
                                                     
                                                     x₁' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₁ (PE Q x₂)))
                                                     x₁' = lemFmap∞ inj₂ Ass⊎ᵣ (fmap∞ inj₁ (PE Q x₂)) l m x'
                                                     
                                                     x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₁) (PE Q x₂))
                                                     x₂' = lemFmap∞ inj₁ (Ass⊎ᵣ ∘ inj₂) (PE Q x₂) l m x₁'
                                                     
                                                     x₃' : Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₂ (PE Q x₂)))
                                                     x₃' = lemFmap∞R inj₂ inj₁ (PE Q x₂) l m x₂'
                                                     
                                                    in extc l m x₂ x₃'
 A□-+- Q x₁ x l m (intc .l .m x₂ x₃) = intc l m x₂ (A□-∞- (PI Q x₂) m l x x₁ x₃)
 A□-+- Q x₁ x .[] .(just (inj₁ (inj₁ x))) (terc (inj₁ x₂)) = terc (inj₂ (inj₁ x₂))
 A□-+- Q x₁ x .[] .(just (inj₂ x₁)) (terc (inj₂ (inj₁ zero))) = terc (inj₁ zero)
 A□-+- Q x₁ x .[] .(just (inj₂ x₁)) (terc (inj₂ (inj₁ (suc ()))))
 A□-+- Q x₁ x .[] .(just (inj₁ (inj₂ (PT Q y)))) (terc (inj₂ (inj₂ y))) = terc (inj₂ (inj₂ y))



 A□+-- : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → (x₂ : Tr+ l m (fmap+ Ass⊎ᵣ (P □++ fmap+ unifyA⊎A (2-✓+ (inj₁ x₁) (inj₂ x)))))
         →  Tr+ l m ((addTimed✓+ (inj₂ x) (fmap+ inj₁ (addTimed✓+ (inj₂ x₁) (fmap+ inj₁ P)))))
 A□+-- P .nothing .[] x x₁ empty = empty
 A□+-- P m .(Lab P x₂ ∷ l) x x₁ (extc l .m (inj₁ x₂) x₃) = let
                                                            x' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x₂)))
                                                            x' = x₃
                                                            
                                                            x₁' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₁) (PE P x₂))
                                                            x₁' = lemFmap∞ inj₁ Ass⊎ᵣ (PE P x₂) l m x'
                                                            
                                                            x₂' :   Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₁ (PE P x₂)))
                                                            x₂' = lemFmap∞R inj₁ inj₁ (PE P x₂) l m x₁'
                                                            
                                                           in extc l m x₂ x₂'
 A□+-- P m .(efq _ ∷ l) x x₁ (extc l .m (inj₂ ()) x₃)
 A□+-- P m l x x₁ (intc .l .m (inj₁ x₂) x₃) = intc l m x₂ (A□∞-- (PI P x₂) m l x x₁ x₃)
 A□+-- P m l x x₁ (intc .l .m (inj₂ ()) x₃)
 A□+-- P .(just (inj₁ (inj₁ (PT P x₂)))) .[] x x₁ (terc (inj₁ x₂)) = terc (inj₂ (inj₂ x₂))
 A□+-- P .(just (inj₁ (inj₂ x₁))) .[] x x₁ (terc (inj₂ zero)) = terc (inj₂ (inj₁ zero))
 A□+-- P .(just (inj₂ x)) .[] x x₁ (terc (inj₂ (suc zero))) = terc (inj₁ zero)
 A□+-- P .(just (Ass⊎ᵣ (inj₂ (unifyA⊎A (if suc (suc _) then inj₁ (inj₁ x₁) else (inj₂ (inj₂ x))))))) .[] x x₁ (terc (inj₂ (suc (suc ()))))


 A□+--ₛ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → (x₂ : Tr+ l m (fmap+ Ass⊎ᵣ (P □++ fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x)))))
         →  Tr+ l m (fmap+ Ass⊎ᵣ (P □++ fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ x₁))))
 A□+--ₛ P .nothing .[] x x₁ empty = empty
 A□+--ₛ P m .(Lab P x₂ ∷ l) x x₁ (extc l .m (inj₁ x₂) x₃) =  let
                                                            x' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x₂)))
                                                            x' = x₃
                                                            
                                                            x₁' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₁) (PE P x₂))
                                                            x₁' =  lemFmap∞ inj₁ Ass⊎ᵣ (PE P x₂) l m x'
                                                            
                                                            x₂' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x₂)))
                                                            x₂' =   lemFmap∞R inj₁ Ass⊎ᵣ (PE P x₂) l m x₁'
                                                            
                                                           in extc l m (inj₁ x₂) x₂'
 A□+--ₛ P m .(efq _ ∷ l) x x₁ (extc l .m (inj₂ ()) x₃)
 A□+--ₛ P m l x x₁ (intc .l .m (inj₁ x₂) x₃) = intc l m (inj₁ x₂) (A□∞--ₛ (PI P x₂) m l x x₁ x₃)
 A□+--ₛ P m l x x₁ (intc .l .m (inj₂ ()) x₃)
 A□+--ₛ P .(just (inj₁ (inj₁ (PT P x₂)))) .[] x x₁ (terc (inj₁ x₂)) = terc (inj₁ x₂)
 A□+--ₛ P .(just (inj₂ x₁)) .[] x x₁ (terc (inj₂ zero)) = terc (inj₂ (suc zero))
 A□+--ₛ P .(just (inj₁ (inj₂ x))) .[] x x₁ (terc (inj₂ (suc zero))) = terc (inj₂ zero)
 A□+--ₛ P .(just (Ass⊎ᵣ (inj₂ (unifyA⊎A (if suc (suc _) then inj₁ (inj₂ x₁)
                                          else (inj₂ (inj₁ x))))))) .[] x x₁ (terc (inj₂ (suc (suc ()))))

 A□--+  : {c₀ c₁ c₂ : Choice}(Z : Process+ ∞ c₂)
         → (q   : ChoiceSet c₁)
         → (x   : ChoiceSet c₀)
         → (l : List Label)
         → (m :  Maybe ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → (tr  : Tr+ l m (fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (addTimed✓+ (inj₁ q) (fmap+ inj₂ Z))))))
         →  Tr+ l m (fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ q)) □++ Z)
 A□--+ Z q x .[] .nothing empty = empty
 A□--+ Z q x .(Lab Z x₁ ∷ l) m (extc l .m x₁ x₂) = let
                                                    x' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₂ (PE Z x₁))))
                                                    x' =  x₂
                                                           
                                                    x₁' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₂ (PE Z x₁)))
                                                    x₁' = lemFmap∞ inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z x₁)) l m x' 
                                                           
                                                    x₂' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₂) (PE Z x₁))
                                                    x₂' =  lemFmap∞ inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z x₁) l m x₁'
                                                           
                                                   in extc l m (inj₂ x₁) x₂'
                                                          
 A□--+ Z q x l m (intc .l .m x₁ x₂) = intc l m (inj₂ x₁) (A□--∞ (PI Z x₁) q x l m x₂)
 A□--+ Z q x .[] .(just (inj₁ (inj₁ x))) (terc (inj₁ zero)) = terc (inj₁ zero)
 A□--+ Z q x .[] .(just (inj₁ (inj₁ x))) (terc (inj₁ (suc ()))) 
 A□--+ Z q x .[] .(just (inj₁ (inj₂ q))) (terc (inj₂ (inj₁ zero))) = terc (inj₁ (suc zero))
 A□--+ Z q x .[] .(just (inj₁ (inj₂ q))) (terc (inj₂ (inj₁ (suc ()))))
 A□--+ Z q x .[] .(just (inj₂ (PT Z y))) (terc (inj₂ (inj₂ y))) = terc (inj₂ y)


 A□--+ₛ  : {c₀ c₁ c₂ : Choice}(Z : Process+ ∞ c₂)
         → ( x  : ChoiceSet c₀)
         → (x₁  : ChoiceSet c₁)
         → (l : List Label)
         → (m :  Maybe ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → ( x₂  : Tr+ l m (fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (addTimed✓+ (inj₁ x₁) (fmap+ inj₂ Z))))))
         →  Tr l m (node (fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x)) □++ Z))
 A□--+ₛ Z x x₁ .[] .nothing empty = tnode empty
 A□--+ₛ Z x x₁ .(Lab Z x₂ ∷ l) m (extc l .m x₂ x₃) = let
                                                       x' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₂ (PE Z x₂))))
                                                       x' =  x₃
                                                           
                                                       x₁' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₂ (PE Z x₂)))
                                                       x₁' = lemFmap∞ inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z x₂)) l m x' 
                                                           
                                                       x₂' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₂) (PE Z x₂))
                                                       x₂' = lemFmap∞ inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z x₂) l m x₁'
                                                           
                                                     in tnode (extc l m (inj₂ x₂) x₂')
                                                   
 A□--+ₛ Z x x₁ l m (intc .l .m x₂ x₃) = tnode (intc l m (inj₂ x₂) (A□--∞ₛ (PI Z x₂) x₁ x l m x₃))
 A□--+ₛ Z x x₁ .[] .(just (inj₁ (inj₁ x))) (terc (inj₁ zero)) = tnode (terc (inj₁ (suc zero)))
 A□--+ₛ Z x x₁ .[] .(just (inj₁ (inj₁ x))) (terc (inj₁ (suc ())))
 A□--+ₛ Z x x₁ .[] .(just (inj₁ (inj₂ x₁))) (terc (inj₂ (inj₁ zero))) = tnode (terc (inj₁ zero))
 A□--+ₛ Z x x₁ .[] .(just (inj₁ (inj₂ x₁))) (terc (inj₂ (inj₁ (suc ()))))
 A□--+ₛ Z x x₁ .[] .(just (inj₂ (PT Z y))) (terc (inj₂ (inj₂ y))) = tnode (terc (inj₂ y))



mutual 
 A□+ᵣ : {c₀ c₁ c₂ : Choice}  (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁) (Z : Process+ ∞ c₂)
        →  fmap+ Ass⊎ᵣ (P □++ (Q  □++ Z ))  ⊑+ ((P □++ Q) □++ Z)
 A□+ᵣ P Q Z .[] .nothing empty = empty
 A□+ᵣ P Q Z .(Lab P x ∷ l) m (extc l .m (inj₁ (inj₁ x)) x₁) = let
                                                                                                         
                                                       x' : Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₁ (PE P x)))
                                                       x' = x₁

                                                       x₁' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₁) (PE P x))
                                                       x₁' = lemFmap∞ inj₁ inj₁ (PE P x) l m x'

                                                       x₂' :  Tr∞ l m (PE (fmap+ Ass⊎ᵣ (P □++ (Q □++ Z))) (inj₁ x))
                                                       x₂' = lemFmap∞R inj₁ Ass⊎ᵣ (PE P x) l m x₁'
                                                       
                                                      in extc l m (inj₁ x) x₂' 
 A□+ᵣ P Q Z .(Lab Q y ∷ l) m (extc l .m (inj₁ (inj₂ y)) x₁) = let

                                                       x' : Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₂ (PE Q y)))
                                                       x' = x₁

                                                       x₁' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₁) (PE Q y))
                                                       x₁' = lemFmap∞ inj₂ inj₁ (PE Q y) l m x'

                                                       x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₁ (PE Q y)))
                                                       x₂' = lemFmap∞R inj₁ (Ass⊎ᵣ ∘ inj₂) (PE Q y) l m x₁'
                                                       
                                                       x₃' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₁ (PE Q y))))
                                                       x₃' = lemFmap∞R inj₂ Ass⊎ᵣ (fmap∞ inj₁ (PE Q y)) l m x₂'
                                                       
                                                      in extc l m (inj₂ (inj₁ y)) x₃'
                                                     
 A□+ᵣ P Q Z .(Lab Z y ∷ l) m (extc l .m (inj₂ y) x₁) = let
                                                        x' :  Tr∞ l m (fmap∞ inj₂ (PE Z y))
                                                        x' =  x₁

                                                        x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₂ (PE Z y))) 
                                                        x₂' = lemFmap∞R inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z y) l m x'                                                                                                               
                                                        x₃' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₂ (PE Z y)))) 
                                                        x₃' = lemFmap∞R inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z y)) l m x₂'                                                                                                                                                                      
                                                       in extc l m (inj₂ (inj₂ y)) x₃'

 A□+ᵣ P Q Z l m (intc .l .m (inj₁ (inj₁ x)) x₁) = intc l m (inj₁ x) (A□∞++ᵣ (PI P x) Q Z l m x₁)
 A□+ᵣ P Q Z l m (intc .l .m (inj₁ (inj₂ y)) x₁) = intc l m (inj₂ (inj₁ y)) (A□+∞+ᵣ P (PI Q y) Z l m x₁)
 A□+ᵣ P Q Z l m (intc .l .m (inj₂ y) x₁) = intc l m (inj₂ (inj₂ y)) (A□++∞ᵣ P Q (PI Z y) l m x₁)
 A□+ᵣ P Q Z .[] .(just (inj₁ (inj₁ (PT P x)))) (terc (inj₁ (inj₁ x))) = terc (inj₁ x)
 A□+ᵣ P Q Z .[] .(just (inj₁ (inj₂ (PT Q y)))) (terc (inj₁ (inj₂ y))) = terc (inj₂ (inj₁ y))
 A□+ᵣ P Q Z .[] .(just (inj₂ (PT Z y))) (terc (inj₂ y)) = terc (inj₂ (inj₂ y))


 A□∞++ᵣ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                            (Q : Process+ ∞ c₁)
                            (Z : Process+ ∞ c₂)
         → Ref∞  (fmap∞ Ass⊎ᵣ ( P □∞++ (Q □++ Z))) (((P □∞++ Q) □∞++ Z))
 forcet (A□∞++ᵣ P Q Z l m x) = tnode (A□+ppᵣ (forcep P) Q Z l m (forcet' l m (forcet x)))



 A□+∞+ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                            (Q : Process∞ ∞ c₁)
                            (Z : Process+ ∞ c₂)
         → Ref∞  (fmap∞ Ass⊎ᵣ ( P □+∞+ (Q □∞++ Z))) (((P □+∞+ Q) □∞++ Z))
 forcet (A□+∞+ᵣ P Q Z l m x) = tnode (A□p+pᵣ P (forcep Q) Z l m (forcet' l m (forcet x)))


 A□++∞ᵣ  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                             (Q : Process+ ∞ c₁)
                             (Z : Process∞ ∞ c₂)
         → Ref∞  (fmap∞ Ass⊎ᵣ ( P □+∞+ (Q □+∞+ Z))) (((P □++ Q) □+∞+ Z))
 forcet (A□++∞ᵣ P Q Z l m x)  = tnode (A□pp+ᵣ P Q (forcep Z) l m (forcet' l m (forcet x)))


 A□+ppᵣ  : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                             (Q : Process+ ∞ c₁)
                             (Z : Process+ ∞ c₂)
         →  Ref+  (fmap+ Ass⊎ᵣ ( P □p++ (Q □++ Z))) (((P □p++ Q) □++ Z))
 A□+ppᵣ (terminate x) Q Z l m tr = A□-++ᵣ Q Z x l m tr
 A□+ppᵣ (node x) Q Z l m tr      = A□+ᵣ x Q Z l m tr


 A□p+pᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                            (Q : Process  ∞ c₁)
                            (Z : Process+ ∞ c₂)
         →  Ref+  (fmap+ Ass⊎ᵣ ( P □++ (Q □p++ Z))) (((P □+p+ Q) □++ Z))
 A□p+pᵣ P (terminate x) Z l m tr = A□+-+ᵣ P Z x l m tr
 A□p+pᵣ P (node x) Z l m tr      = A□+ᵣ P x Z l m tr


 A□pp+ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                            (Q : Process+ ∞ c₁)
                            (Z : Process  ∞ c₂)
         →  Ref+  (fmap+ Ass⊎ᵣ ( P □++ (Q □+p+ Z))) (((P □++ Q) □+p+ Z))
 A□pp+ᵣ P Q (terminate x) l m tr =  A□++-ᵣ P Q m l x tr
 A□pp+ᵣ P Q (node x) l m tr      =  A□+ᵣ   P Q x  l m tr


 A□++-ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                            (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → ( x : ChoiceSet c₂ )
         → (tr :  Tr+ l m (addTimed✓+ (inj₂ x) (fmap+ inj₁ (P □++ Q))))
         →  Tr+ l m (fmap+ Ass⊎ᵣ (P □++ addTimed✓+ (inj₂ x) (fmap+ inj₁ Q)))
 A□++-ᵣ P Q .nothing .[] x empty = empty
 A□++-ᵣ P Q m .(Lab P x₁ ∷ l) x (extc l .m (inj₁ x₁) x₂) = let
                                                            x'  : Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₁ (PE P x₁)))
                                                            x'  = x₂
                                                            
                                                            x'₃  : Tr∞ l m (fmap∞ (inj₁ ∘ inj₁) (PE P x₁))
                                                            x'₃  = lemFmap∞ inj₁ inj₁ (PE P x₁) l m x'

                                                            x₁' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₁) (PE P x₁))
                                                            x₁' =  lemFmap∞ inj₁ inj₁ (PE P x₁) l m x'
                                                            
                                                            x₂' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x₁)))
                                                            x₂' = lemFmap∞R inj₁ Ass⊎ᵣ (PE P x₁) l m x₁'
                                                            
                                                          in extc l m (inj₁ x₁) x₂'

 A□++-ᵣ P Q m .(Lab Q y ∷ l) x (extc l .m (inj₂ y) x₂) = let

                                                       x' : Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₂ (PE Q y)))
                                                       x' = x₂

                                                       x₁' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₁) (PE Q y))
                                                       x₁' = lemFmap∞ inj₂ inj₁ (PE Q y) l m x'

                                                       x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₁ (PE Q y)))
                                                       x₂' = lemFmap∞R inj₁ (Ass⊎ᵣ ∘ inj₂) (PE Q y) l m x₁'
                                                       
                                                       x₃' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₁ (PE Q y))))
                                                       x₃' = lemFmap∞R inj₂ Ass⊎ᵣ (fmap∞ inj₁ (PE Q y)) l m x₂'
                                                       
                                                      in extc l m  (inj₂ y) x₃'
 A□++-ᵣ P Q m l x (intc .l .m (inj₁ x₁) x₂) =  intc l m (inj₁ x₁) (A□∞+-ᵣ (PI P x₁) Q m l x x₂)
 A□++-ᵣ P Q m l x (intc .l .m (inj₂ y) x₂) =  intc l m (inj₂ y) (A□+∞-ᵣ P (PI Q y) m l x x₂)
 A□++-ᵣ P Q .(just (inj₂ x)) .[] x (terc (inj₁ zero)) = terc (inj₂ (inj₁ zero))
 A□++-ᵣ P Q .(just (inj₂ x)) .[] x (terc (inj₁ (suc ())))
 A□++-ᵣ P Q .(just (inj₁ (inj₁ (PT P x₁)))) .[] x (terc (inj₂ (inj₁ x₁))) = terc (inj₁ x₁)
 A□++-ᵣ P Q .(just (inj₁ (inj₂ (PT Q y)))) .[] x (terc (inj₂ (inj₂ y))) = terc (inj₂ (inj₂ y))


 A□-++ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → (x   : ChoiceSet c₀)
         → (l : List Label)
         → (m : Maybe ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → (tr  :  Tr+ l m (addTimed✓+ (inj₁ x) (fmap+ inj₂ Q) □++ Z))
         →  Tr+ l m (fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (Q □++ Z))))
 A□-++ᵣ Q Z x .[] .nothing empty = empty
 A□-++ᵣ Q Z x .(Lab Q x₁ ∷ l) m (extc l .m (inj₁ x₁) x₂) = (let
                                                                  x' : Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₂ (PE Q x₁)))
                                                                  x' = x₂
                                                                  
                                                                  x₁' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₁) (PE Q x₁))
                                                                  x₁' = lemFmap∞ inj₂ inj₁ (PE Q x₁) l m x'
                                                                  
                                                                  x₂' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₁ (PE Q x₁)))
                                                                  x₂' = lemFmap∞R inj₁ (Ass⊎ᵣ ∘ inj₂) (PE Q x₁) l m x₁'
                                                                  
                                                                  x₃' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₁ (PE Q x₁))))
                                                                  x₃' = lemFmap∞R inj₂ Ass⊎ᵣ (fmap∞ inj₁ (PE Q x₁)) l m x₂'
                                                                  
                                                              in extc l m (inj₁ x₁) x₃' )
                                                             
 A□-++ᵣ Q Z x .(Lab Z y ∷ l) m (extc l .m (inj₂ y) x₂) =  let
                                                        x' :  Tr∞ l m (fmap∞ inj₂ (PE Z y))
                                                        x' =  x₂

                                                        x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₂ (PE Z y))) 
                                                        x₂' = lemFmap∞R inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z y) l m x'                                                                                                               
                                                        x₃' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₂ (PE Z y)))) 
                                                        x₃' = lemFmap∞R inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z y)) l m x₂'                                                                                                                                                                      
                                                       in extc l m ((inj₂ y)) x₃'
                                                       
 A□-++ᵣ Q Z x l m (intc .l .m (inj₁ x₁) x₂) = intc l m (inj₁ x₁) (A□-∞+ᵣ (PI Q x₁) Z x l m x₂)
 A□-++ᵣ Q Z x l m (intc .l .m (inj₂ y) x₂) =  intc l m (inj₂ y) (A□-+∞ᵣ Q (PI Z y) x l m x₂)
 A□-++ᵣ Q Z x .[] .(just (inj₁ (inj₁ x))) (terc (inj₁ (inj₁ zero))) = terc (inj₁ zero)
 A□-++ᵣ Q Z x .[] .(just (inj₁ (inj₁ x))) (terc (inj₁ (inj₁ (suc ()))))
 A□-++ᵣ Q Z x .[] .(just (inj₁ (inj₂ (PT Q y)))) (terc (inj₁ (inj₂ y))) = terc (inj₂ (inj₁ y))
 A□-++ᵣ Q Z x .[] .(just (inj₂ (PT Z y))) (terc (inj₂ y)) = terc (inj₂ (inj₂ y))



 A□+-+ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → ( tr  :  Tr+ l m (addTimed✓+ (inj₂ x) (fmap+ inj₁ P) □++ Z))
         →  Tr+ l m (fmap+ Ass⊎ᵣ (P □++ addTimed✓+ (inj₁ x) (fmap+ inj₂ Z)))
 A□+-+ᵣ P Z x .[] .nothing empty = empty
 A□+-+ᵣ P Z x .(Lab P x₁ ∷ l) m (extc l .m (inj₁ x₁) x₂) = let
                                                            x'  : Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₁ (PE P x₁)))
                                                            x'  = x₂
                                                            
                                                            x'₃  : Tr∞ l m (fmap∞ (inj₁ ∘ inj₁) (PE P x₁))
                                                            x'₃  = lemFmap∞ inj₁ inj₁ (PE P x₁) l m x'

                                                            x₁' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₁) (PE P x₁))
                                                            x₁' =  lemFmap∞ inj₁ inj₁ (PE P x₁) l m x'
                                                            
                                                            x₂' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x₁)))
                                                            x₂' = lemFmap∞R inj₁ Ass⊎ᵣ (PE P x₁) l m x₁'
                                                            
                                                          in extc l m (inj₁ x₁) x₂'
 A□+-+ᵣ P Z x .(Lab Z y ∷ l) m (extc l .m (inj₂ y) x₂) = let
                                                        x' :  Tr∞ l m (fmap∞ inj₂ (PE Z y))
                                                        x' =  x₂

                                                        x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₂ (PE Z y))) 
                                                        x₂' = lemFmap∞R inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z y) l m x'                                                                                                               
                                                        x₃' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₂ (PE Z y)))) 
                                                        x₃' = lemFmap∞R inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z y)) l m x₂'                                                                                                                                                                      
                                                       in extc l m ((inj₂ y)) x₃'
 A□+-+ᵣ P Z x l m (intc .l .m (inj₁ x₁) x₂) =  intc l m (inj₁ x₁) (A□∞-+ᵣ (PI P x₁) Z x l m x₂)
 A□+-+ᵣ P Z x l m (intc .l .m (inj₂ y) x₂) =  intc l m (inj₂ y) (A□+-∞ᵣ P (PI Z y) x l m x₂)
 A□+-+ᵣ P Z x .[] .(just (inj₁ (inj₂ x))) (terc (inj₁ (inj₁ x₁))) = terc (inj₂ (inj₁ zero))
 A□+-+ᵣ P Z x .[] .(just (inj₁ (inj₁ (PT P y)))) (terc (inj₁ (inj₂ y))) = terc (inj₁ y)
 A□+-+ᵣ P Z x .[] .(just (inj₂ (PT Z y))) (terc (inj₂ y)) = terc (inj₂ (inj₂ y))


 A□+∞-ᵣ  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                               (Q : Process∞ ∞ c₁)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂  :  Tr∞ l m (addTimed✓∞ (inj₂ x) (fmap∞ inj₁ (P □+∞+ Q ))))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (P □+∞+ addTimed✓∞ (inj₂ x) (fmap∞ inj₁ (Q ))))
 forcet (A□+∞-ᵣ P Q m l x x₂) = tnode (A□+p-ᵣ P (forcep Q) m l x (forcet' l m (forcet x₂))) 


 A□∞+-ᵣ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                            (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂  : Tr∞ l m (addTimed✓∞ (inj₂ x) (fmap∞ inj₁ (P □∞++ Q))))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (P □∞++ addTimed✓+ (inj₂ x) (fmap+ inj₁ Q)))
 forcet ( A□∞+-ᵣ P Q m l x x₂) = tnode (A□p+-ᵣ (forcep P) Q m l x (forcet' l m (forcet x₂)))



 A□-∞+ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process∞ ∞ c₁)
                            (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → (x₂ : Tr∞ l m (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ Q) □∞++ Z))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (Q □∞++ Z))))
 forcet (A□-∞+ᵣ Q Z x l m tr) = A□-p+ᵣ (forcep Q) Z x l m (forcet tr) 

 A□∞-+ᵣ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                            (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → ( x₂  : Tr∞ l m (addTimed✓∞ (inj₂ x) (fmap∞ inj₁ (P)) □∞++ Z))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (P □∞++ addTimed✓+ (inj₁ x) (fmap+ inj₂ Z)))
 forcet (A□∞-+ᵣ P Z x l m x₂) =  tnode (A□p-+ᵣ ((forcep P)) Z x l m (forcet x₂))



 A□+-∞ᵣ  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                             (Z : Process∞ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  :  Tr∞ l m (addTimed✓+ (inj₂ x) (fmap+ inj₁ P) □+∞+ Z))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (P □+∞+ addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (Z))))
 forcet (A□+-∞ᵣ  P Z x l m x₂) = A□+-pᵣ P (forcep Z) x l m (forcet x₂)


 A□-+∞ᵣ  : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                             (Z : Process∞ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  : Tr∞ l m (addTimed✓+ (inj₁ x) (fmap+ inj₂ Q) □+∞+ Z ))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (Q □+∞+ Z))))
 forcet (A□-+∞ᵣ  Q Z x l m tr) = tnode ( A□-+pᵣ Q (forcep Z) x l m (forcet' l m (forcet tr)))



 A□p+-ᵣ : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                              (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂  :  Tr+ l m ((addTimed✓+ (inj₂ x) (fmap+ inj₁ (P □p++ Q)))))
         →  Tr+ l m (fmap+ Ass⊎ᵣ (P □p++ addTimed✓+ (inj₂ x) (fmap+ inj₁ Q)))
 A□p+-ᵣ (terminate x) Q m l x₁ x₂ = A□-+-ᵣ Q x₁ x l m x₂
 A□p+-ᵣ (node x) Q m l x₁ x₂      = A□++-ᵣ x Q m l x₁ x₂

 A□+p-ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process  ∞ c₁)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂  : Tr+ l m ((addTimed✓+ (inj₂ x) (fmap+ inj₁ (P □+p+ Q)))))
         →  Tr+ l m (fmap+ Ass⊎ᵣ (P □+p+ addTimed✓ (inj₂ x) (fmap inj₁ Q)))
 A□+p-ᵣ P (terminate x) m l x₁ x₂ = A□+--ᵣ P m l x x₁ x₂
 A□+p-ᵣ P (node x) m l x₁ x₂      = A□++-ᵣ P x m l x₁ x₂ 


 A□+-pᵣ  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                             (Z : Process  ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → ( x₂ : Tr l m (node (addTimed✓+ (inj₂ x) (fmap+ inj₁ P) □+p+ Z)))
         →   Tr l m (node (fmap+ Ass⊎ᵣ (P □+p+ addTimed✓ (inj₁ x) (fmap inj₂ Z))))
 A□+-pᵣ  P (terminate x) x₁ l m x₂ = tnode (A□+--ᵣᵣ P m l x₁ x x₂)
 A□+-pᵣ  P (node x) x₁ l m x₂      = tnode (A□+-+ᵣ P x x₁ l m (forcet' l m x₂))


 A□-+pᵣ : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                            (Z : Process  ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeExtC) 
         → (tr  :  Tr+ l m ((addTimed✓+ (inj₁ x) (fmap+ inj₂ Q) □+p+ Z)))
         →  Tr+ l m ((fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (Q □+p+ Z)))))
 A□-+pᵣ Q (terminate x) x₁ l m tr =  A□-+-ᵣ Q x x₁ l m tr 
 A□-+pᵣ Q (node x) x₁ l m tr      =  A□-++ᵣ Q x x₁ l m tr

 A□p-+ᵣ : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                            (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  :  Tr l m (node (addTimed✓ (inj₂ x) (fmap inj₁ P) □p++ Z)))
         →  Tr+ l m ((fmap+ Ass⊎ᵣ (P □p++ addTimed✓+ (inj₁ x) (fmap+ inj₂ Z))))
 A□p-+ᵣ (terminate x) Z x₁ l m x₂ = A□--+ᵣᵣ Z x₁ x l m x₂
 A□p-+ᵣ (node x) Z x₁ l m x₂      = A□+-+ᵣ x Z x₁ l m (forcet' l m x₂)

 A□-p+ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process  ∞ c₁)
                            (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe  ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → (tr  :  Tr l m (node (addTimed✓ (inj₁ x) (fmap inj₂ Q) □p++ Z)))
         →  Tr l m (node (fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (Q □p++ Z)))))
 A□-p+ᵣ (terminate q) Z x l m tr = tnode (A□--+ᵣᵣᵣᵣ Z q x l m tr)
 A□-p+ᵣ (node q) Z x l m tr      = tnode (A□-++ᵣ q Z x l m (forcet' l m tr))

 A□-+-ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
         → (x₁ : ChoiceSet c₀)
         → (x  : ChoiceSet c₂)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → ( x₂  : Tr+ l m (addTimed✓+ (inj₂ x₁) (fmap+ inj₁ (addTimed✓+ (inj₁ x) (fmap+ inj₂ Q)))))
         →  Tr+ l m (fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (addTimed✓+ (inj₂ x₁) (fmap+ inj₁ Q)))))
 A□-+-ᵣ Q x₁ x .[] .nothing empty = empty
 A□-+-ᵣ Q x₁ x .(Lab Q x₂ ∷ l) m (extc l .m x₂ x₃) =  let
                                                                  x' : Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₂ (PE Q x₂)))
                                                                  x' = x₃
                                                                  
                                                                  x₁' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂ ∘ inj₁) (PE Q x₂))
                                                                  x₁' = lemFmap∞ inj₂ inj₁ (PE Q x₂) l m x'
                                                                  
                                                                  x₂' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₁ (PE Q x₂)))
                                                                  x₂' = lemFmap∞R inj₁ (Ass⊎ᵣ ∘ inj₂) (PE Q x₂) l m x₁'
                                                                  
                                                                  x₃' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₁ (PE Q x₂))))
                                                                  x₃' = lemFmap∞R inj₂ Ass⊎ᵣ (fmap∞ inj₁ (PE Q x₂)) l m x₂'
                                                                  
                                                              in extc l m x₂ x₃'
 A□-+-ᵣ Q x₁ x l m (intc .l .m x₂ x₃) = intc l m x₂ (A□-∞-ᵣ (PI Q x₂) m l x x₁ x₃)
 A□-+-ᵣ Q x₁ x .[] .(just (inj₂ x₁)) (terc (inj₁ zero)) = terc (inj₂ (inj₁ zero))
 A□-+-ᵣ Q x₁ x .[] .(just (inj₂ x₁)) (terc (inj₁ (suc ())))
 A□-+-ᵣ Q x₁ x .[] .(just (inj₁ (inj₁ x))) (terc (inj₂ (inj₁ zero))) = terc (inj₁ zero)
 A□-+-ᵣ Q x₁ x .[] .(just (inj₁ (inj₁ x))) (terc (inj₂ (inj₁ (suc ()))))
 A□-+-ᵣ Q x₁ x .[] .(just (inj₁ (inj₂ (PT Q y)))) (terc (inj₂ (inj₂ y))) = terc (inj₂ (inj₂ y))


 A□+--ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → (x₂ :  Tr+ l m (addTimed✓+ (inj₂ x₁)(fmap+ inj₁ (addTimed✓+ (inj₂ x) (fmap+ inj₁ P)))))
         →  Tr+ l m (fmap+ Ass⊎ᵣ (P □++ fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x))))
 A□+--ᵣ P .nothing .[] x x₁ empty = empty
 A□+--ᵣ P m .(Lab P x₂ ∷ l) x x₁ (extc l .m x₂ x₃) =  let
                                                            x'  : Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₁ (PE P x₂)))
                                                            x'  = x₃
                                                            
                                                            x'₃  : Tr∞ l m (fmap∞ (inj₁ ∘ inj₁) (PE P x₂))
                                                            x'₃  = lemFmap∞ inj₁ inj₁ (PE P x₂) l m x'

                                                            x₁' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₁) (PE P x₂))
                                                            x₁' =  lemFmap∞ inj₁ inj₁ (PE P x₂) l m x'
                                                            
                                                            x₂' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x₂)))
                                                            x₂' = lemFmap∞R inj₁ Ass⊎ᵣ (PE P x₂) l m x₁'
                                                            
                                                          in extc l m (inj₁ x₂) x₂'
 A□+--ᵣ P m l x x₁ (intc .l .m x₂ x₃) = intc l m (inj₁ x₂) (A□∞--ᵣᵣ (PI P x₂) m l x x₁ x₃)
 A□+--ᵣ P .(just (inj₂ x₁)) .[] x x₁ (terc (inj₁ zero)) = terc (inj₂ zero)
 A□+--ᵣ P .(just (inj₂ x₁)) .[] x x₁ (terc (inj₁ (suc ())))
 A□+--ᵣ P .(just (inj₁ (inj₂ x))) .[] x x₁ (terc (inj₂ (inj₁ zero))) = terc (inj₂ (suc zero))
 A□+--ᵣ P .(just (inj₁ (inj₂ x))) .[] x x₁ (terc (inj₂ (inj₁ (suc ()))))
 A□+--ᵣ P .(just (inj₁ (inj₁ (PT P y)))) .[] x x₁ (terc (inj₂ (inj₂ y))) = terc (inj₁ y)

 A□+--ᵣᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x₁  : ChoiceSet c₁)
         → (x   : ChoiceSet c₂)
         → (x₂ :  Tr l m (node (addTimed✓+ (inj₂ x) (fmap+ inj₁ (addTimed✓+ (inj₂ x₁) (fmap+ inj₁ P))))))
         →   Tr+ l m (fmap+ Ass⊎ᵣ (P □++ fmap+ unifyA⊎A (2-✓+ (inj₁ x₁) (inj₂ x))))
 A□+--ᵣᵣ P .nothing .[] x x₁ (tnode empty) = empty
 A□+--ᵣᵣ P m .(Lab P x₂ ∷ l) x x₁ (tnode (extc l .m x₂ x₃)) = let
                                                            x'  : Tr∞ l m (fmap∞ inj₁ (fmap∞ inj₁ (PE P x₂)))
                                                            x'  = x₃
                                                            
                                                            x'₃  : Tr∞ l m (fmap∞ (inj₁ ∘ inj₁) (PE P x₂))
                                                            x'₃  = lemFmap∞ inj₁ inj₁ (PE P x₂) l m x'

                                                            x₁' : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₁) (PE P x₂))
                                                            x₁' =  lemFmap∞ inj₁ inj₁ (PE P x₂) l m x'
                                                            
                                                            x₂' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x₂)))
                                                            x₂' = lemFmap∞R inj₁ Ass⊎ᵣ (PE P x₂) l m x₁'
                                                            
                                                          in extc l m (inj₁ x₂) x₂'
 A□+--ᵣᵣ P m l x x₁ (tnode (intc .l .m x₂ x₃)) = intc l m (inj₁ x₂) (A□∞--ᵣ (PI P x₂) m l x₁ x x₃)
 A□+--ᵣᵣ P .(just (inj₂ x₁)) .[] x x₁ (tnode (terc (inj₁ zero))) = terc (inj₂ (suc zero))
 A□+--ᵣᵣ P .(just (inj₂ x₁)) .[] x x₁ (tnode (terc (inj₁ (suc ()))))
 A□+--ᵣᵣ P .(just (inj₁ (inj₂ x))) .[] x x₁ (tnode (terc (inj₂ (inj₁ zero)))) = terc (inj₂ zero)
 A□+--ᵣᵣ P .(just (inj₁ (inj₂ x))) .[] x x₁ (tnode (terc (inj₂ (inj₁ (suc ())))))
 A□+--ᵣᵣ P .(just (inj₁ (inj₁ (PT P y)))) .[] x x₁ (tnode (terc (inj₂ (inj₂ y)))) = terc (inj₁ y)



 A□+--ₛᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → (x₂ :  Tr+ l m (fmap+ Ass⊎ᵣ (P □++ fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ x₁)))))
         →  Tr+ l m (fmap+ Ass⊎ᵣ (P □++ fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x))))
 A□+--ₛᵣ P .nothing .[] x x₁ empty = empty
 A□+--ₛᵣ P m .(Lab P x₂ ∷ l) x x₁ (extc l .m (inj₁ x₂) x₃) =   let
                                                            x'  : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x₂)))
                                                            x'  =  x₃
                                                            
                                                            x'₃  : Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₁) (PE P x₂))
                                                            x'₃  = lemFmap∞ inj₁ Ass⊎ᵣ (PE P x₂) l m x'
                                                            
                                                            x₂' : Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₁ (PE P x₂)))
                                                            x₂' = lemFmap∞R inj₁ Ass⊎ᵣ (PE P x₂) l m x'₃
                                                            
                                                          in extc l m (inj₁ x₂) x₂'
 A□+--ₛᵣ P m .(efq _ ∷ l) x x₁ (extc l .m (inj₂ ()) x₃)
 A□+--ₛᵣ P m l x x₁ (intc .l .m (inj₁ x₂) x₃) = intc l m (inj₁ x₂) (A□∞--ₛᵣ (PI P x₂) m l x x₁ x₃)         
 A□+--ₛᵣ P m l x x₁ (intc .l .m (inj₂ ()) x₃)
 A□+--ₛᵣ P .(just (inj₁ (inj₁ (PT P x₂)))) .[] x x₁ (terc (inj₁ x₂)) = terc (inj₁ x₂)
 A□+--ₛᵣ P .(just (inj₁ (inj₂ x))) .[] x x₁ (terc (inj₂ zero)) = terc (inj₂ (suc zero))
 A□+--ₛᵣ P .(just (inj₂ x₁)) .[] x x₁ (terc (inj₂ (suc zero))) = terc (inj₂ zero)
 A□+--ₛᵣ P .(just (Ass⊎ᵣ (inj₂ (unifyA⊎A (if suc (suc _) then inj₁ (inj₁ x)
                                           else (inj₂ (inj₂ x₁))))))) .[] x x₁ (terc (inj₂ (suc (suc ()))))         
 A□--+ᵣ  : {c₀ c₁ c₂ : Choice}(Z : Process+ ∞ c₂)
         → (q   : ChoiceSet c₁)
         → (x   : ChoiceSet c₀)
         → (l : List Label)
         → (m :  Maybe ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → (tr  :  Tr+ l m (fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ q)) □++ Z))
         →  Tr+ l m (fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (addTimed✓+ (inj₁ q) (fmap+ inj₂ Z)))))
 A□--+ᵣ Z q x .[] .nothing empty = empty
 A□--+ᵣ Z q x .(efq _ ∷ l) m (extc l .m (inj₁ ()) x₂)
 A□--+ᵣ Z q x .(Lab Z y ∷ l) m (extc l .m (inj₂ y) x₂) =  let
                                                        x' : Tr∞ l m (fmap∞ inj₂ (PE Z y))
                                                        x' =   x₂

                                                        x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₂ (PE Z y))) 
                                                        x₂' = lemFmap∞R inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z y) l m x'                                                                                                               
                                                        x₃' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₂ (PE Z y)))) 
                                                        x₃' = lemFmap∞R inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z y)) l m x₂'                                                                                                                                                                      
                                                       in extc l m  y x₃'
 A□--+ᵣ Z q x l m (intc .l .m (inj₁ ()) x₂)
 A□--+ᵣ Z q x l m (intc .l .m (inj₂ y) x₂) = intc l m y (A□--∞ᵣ (PI Z y) q x l m x₂)
 A□--+ᵣ Z q x .[] .(just (inj₁ (inj₁ x))) (terc (inj₁ zero)) = terc (inj₁ zero)
 A□--+ᵣ Z q x .[] .(just (inj₁ (inj₂ q))) (terc (inj₁ (suc zero))) = terc (inj₂ (inj₁ zero))
 A□--+ᵣ Z q x .[] .(just (inj₁ (unifyA⊎A (if suc (suc _) then inj₁ (inj₁ x) else (inj₂ (inj₂ q)))))) (terc (inj₁ (suc (suc ()))))
 A□--+ᵣ Z q x .[] .(just (inj₂ (PT Z y))) (terc (inj₂ y)) = terc (inj₂ (inj₂ y))


 A□--+ᵣᵣ  : {c₀ c₁ c₂ : Choice}(Z : Process+ ∞ c₂)
         → (x₁   : ChoiceSet c₁)
         → (x   : ChoiceSet c₀)
         → (l : List Label)
         → (m :  Maybe ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → (tr  :  Tr l m (node (fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x)) □++ Z)))
         →  Tr+ l m (fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (addTimed✓+ (inj₁ x₁) (fmap+ inj₂ Z)))))
 A□--+ᵣᵣ Z x₁ x .[] .nothing (tnode empty) =  empty
 A□--+ᵣᵣ Z x₁ x .(efq _ ∷ l) m (tnode (extc l .m (inj₁ ()) x₃))
 A□--+ᵣᵣ Z x₁ x .(Lab Z y ∷ l) m (tnode (extc l .m (inj₂ y) x₃)) = let
                                                        x' : Tr∞ l m (fmap∞ inj₂ (PE Z y))
                                                        x' =   x₃

                                                        x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₂ (PE Z y))) 
                                                        x₂' = lemFmap∞R inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z y) l m x'                                                                                                               
                                                        x₃' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₂ (PE Z y)))) 
                                                        x₃' = lemFmap∞R inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z y)) l m x₂'                                                                                                                                                                      
                                                       in extc l m  y x₃'
 A□--+ᵣᵣ Z x₁ x l m (tnode (intc .l .m (inj₁ ()) x₃))
 A□--+ᵣᵣ Z x₁ x l m (tnode (intc .l .m (inj₂ y) x₃)) = intc l m y (A□--∞ᵣᵣᵣ (PI Z y) x x₁ l m x₃)
 A□--+ᵣᵣ Z x₁ x .[] .(just (inj₁ (inj₂ x₁))) (tnode (terc (inj₁ zero))) = terc (inj₂ (inj₁ zero))
 A□--+ᵣᵣ Z x₁ x .[] .(just (inj₁ (inj₁ x))) (tnode (terc (inj₁ (suc zero)))) = terc (inj₁ zero)
 A□--+ᵣᵣ Z x₁ x .[] .(just (inj₁ (unifyA⊎A (if suc (suc _) then inj₁ (inj₂ x₁)
                                            else (inj₂ (inj₁ x)))))) (tnode (terc (inj₁ (suc (suc ())))))
 A□--+ᵣᵣ Z x₁ x .[] .(just (inj₂ (PT Z y))) (tnode (terc (inj₂ y))) = terc (inj₂ (inj₂ y))



 A□--+ᵣᵣᵣᵣ  : {c₀ c₁ c₂ : Choice}(Z : Process+ ∞ c₂)
         → (q   : ChoiceSet c₁)
         → (x   : ChoiceSet c₀)
         → (l : List Label)
         → (m :  Maybe ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → (tr  :  Tr l m (node (fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ q)) □++ Z)))
         →  Tr+ l m ((fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (addTimed✓+ (inj₁ q) (fmap+ inj₂ Z))))))
 A□--+ᵣᵣᵣᵣ Z q x .[] .nothing (tnode empty) = empty
 A□--+ᵣᵣᵣᵣ Z q x .(efq _ ∷ l) m (tnode (extc l .m (inj₁ ()) x₂))
 A□--+ᵣᵣᵣᵣ Z q x .(Lab Z y ∷ l) m (tnode (extc l .m (inj₂ y) x₂)) =  let
                                                        x' : Tr∞ l m (fmap∞ inj₂ (PE Z y))
                                                        x' =   x₂

                                                        x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₂ (PE Z y))) 
                                                        x₂' = lemFmap∞R inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z y) l m x'                                                                                                               
                                                        x₃' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₂ (PE Z y)))) 
                                                        x₃' = lemFmap∞R inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z y)) l m x₂'                                                                                                                                                                      
                                                       in extc l m  y x₃'
 A□--+ᵣᵣᵣᵣ Z q x l m (tnode (intc .l .m (inj₁ ()) x₂))
 A□--+ᵣᵣᵣᵣ Z q x l m (tnode (intc .l .m (inj₂ y) x₂)) = intc l m y (A□--∞ᵣᵣᵣᵣᵣ (PI Z y) x q l m x₂)
 A□--+ᵣᵣᵣᵣ Z q x .[] .(just (inj₁ (inj₁ x))) (tnode (terc (inj₁ zero))) = terc (inj₁ zero)
 A□--+ᵣᵣᵣᵣ Z q x .[] .(just (inj₁ (inj₂ q))) (tnode (terc (inj₁ (suc zero)))) = terc (inj₂ (inj₁ zero))
 A□--+ᵣᵣᵣᵣ Z q x .[] .(just (inj₁ (unifyA⊎A (if suc (suc _) then inj₁ (inj₁ x)
                                            else (inj₂ (inj₂ q)))))) (tnode (terc (inj₁ (suc (suc ())))))
 A□--+ᵣᵣᵣᵣ Z q x .[] .(just (inj₂ (PT Z y))) (tnode (terc (inj₂ y))) = terc (inj₂ (inj₂ y))


 A□--+ₛᵣᵣ  : {c₀ c₁ c₂ : Choice}(Z : Process+ ∞ c₂)
         → ( x  : ChoiceSet c₀)
         → (x₁  : ChoiceSet c₁)
         → (l : List Label)
         → (m :  Maybe ((ChoiceSet c₀ ⊎ ChoiceSet c₁) ⊎ ChoiceSet c₂))
         → ( x₂  :  Tr+ l m ((fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x)) □++ Z)))
         →  Tr l m (node (fmap+ Ass⊎ᵣ (addTimed✓+ (inj₁ x) (fmap+ inj₂ (addTimed✓+ (inj₁ x₁) (fmap+ inj₂ Z))))))
 A□--+ₛᵣᵣ Z x x₁ .[] .nothing empty = tnode empty
 A□--+ₛᵣᵣ Z x x₁ .(efq _ ∷ l) m (extc l .m (inj₁ ()) x₃)
 A□--+ₛᵣᵣ Z x x₁ .(Lab Z y ∷ l) m (extc l .m (inj₂ y) x₃) =  let
                                                        x' : Tr∞ l m (fmap∞ inj₂ (PE Z y))
                                                        x' =   x₃

                                                        x₂' :  Tr∞ l m (fmap∞ (Ass⊎ᵣ ∘ inj₂) (fmap∞ inj₂ (PE Z y))) 
                                                        x₂' = lemFmap∞R inj₂ (Ass⊎ᵣ ∘ inj₂) (PE Z y) l m x'                                                                                                               
                                                        x₃' :  Tr∞ l m (fmap∞ Ass⊎ᵣ (fmap∞ inj₂ (fmap∞ inj₂ (PE Z y)))) 
                                                        x₃' = lemFmap∞R inj₂ Ass⊎ᵣ (fmap∞ inj₂ (PE Z y)) l m x₂'                                                                                                                                                                      
                                                       in tnode (extc l m y x₃')
 A□--+ₛᵣᵣ Z x x₁ l m (intc .l .m (inj₁ ()) x₃)
 A□--+ₛᵣᵣ Z x x₁ l m (intc .l .m (inj₂ y) x₃) = tnode (intc l m y (A□--∞£ᵣᵣᵣᵣᵣᵣᵣᵣ (PI Z y) x x₁ l m x₃))
 A□--+ₛᵣᵣ Z x x₁ .[] .(just (inj₁ (inj₂ x₁))) (terc (inj₁ zero)) = tnode (terc (inj₂ (inj₁ zero)))
 A□--+ₛᵣᵣ Z x x₁ .[] .(just (inj₁ (inj₁ x))) (terc (inj₁ (suc zero))) = tnode (terc (inj₁ zero))
 A□--+ₛᵣᵣ Z x x₁ .[] .(just (inj₁ (unifyA⊎A (if suc (suc _) then inj₁ (inj₂ x₁)
                                               else (inj₂ (inj₁ x)))))) (terc (inj₁ (suc (suc ()))))
 A□--+ₛᵣᵣ Z x x₁ .[] .(just (inj₂ (PT Z y))) (terc (inj₂ y)) = tnode (terc (inj₂ (inj₂ y)))

 A□-∞-ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process∞ ∞ c₁)
         → (m  : Maybe  maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₀)
         → (x₁ : ChoiceSet c₂)
         → (x₃ : Tr∞ l m (addTimed✓∞ (inj₂ x₁) (fmap∞ inj₁ (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (Q))))))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (addTimed✓∞ (inj₂ x₁) (fmap∞ inj₁ (Q))))))
 forcet (A□-∞-ᵣ Q m l x x₁ x₃) = A□-p-ᵣ (forcep Q) x₁ x l m (forcet x₃) 

 A□∞--ᵣ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → ( x₃  : Tr∞ l m (addTimed✓∞ (inj₂ x) (fmap∞ inj₁ (addTimed✓∞ (inj₂ x₁) (fmap∞ inj₁ ( P))))))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (P □∞++ fmap+ unifyA⊎A (2-✓+ (inj₁ x₁) (inj₂ x))))
 forcet (A□∞--ᵣ P m l x x₁ x₃) = A□p--ᵣᵣ (forcep P) x₁ x l m (forcet x₃)


 A□∞--ᵣᵣ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → ( x₃  :  Tr∞ l m (addTimed✓∞ (inj₂ x₁)(fmap∞ inj₁ (addTimed✓∞ (inj₂ x) (fmap∞ inj₁ ( P ))))))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (P □∞++ fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x))))
 forcet (A□∞--ᵣᵣ P m l x x₁ x₃) = A□p--ᵣᵣᵣ (forcep P) x₁ x l m (forcet x₃)



 A□∞--ₛᵣ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
         → (m  : Maybe maybeExtC)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → (x₃  :  Tr∞ l m (fmap∞ Ass⊎ᵣ (P □∞++ fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ x₁)))))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ  (P □∞++ fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x))))
 forcet (A□∞--ₛᵣ P m l x x₁ x₃) = A□p--ₛᵣ (forcep P) x₁ x l m (forcet x₃)


 A□--∞ᵣ : {c₀ c₁ c₂ : Choice}(Z : Process∞ ∞ c₂)
         → (q  : ChoiceSet c₁)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  : Tr∞ l m (fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ q)) □+∞+ Z))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x) (fmap∞ inj₂ (addTimed✓∞ (inj₁ q) (fmap∞ inj₂ Z)))))
 forcet (A□--∞ᵣ Z q x l m x₂) = A□p--ₛᵣᵣᵣᵣ (forcep Z) x q l m (forcet x₂)


 A□--∞ᵣᵣᵣ : {c₀ c₁ c₂ : Choice}(Z : Process∞ ∞ c₂)
         → (x   : ChoiceSet c₀)
         → (x₁  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  :  Tr∞ l m (fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x)) □+∞+ Z))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x)(fmap∞ inj₂ (addTimed✓∞  (inj₁ x₁) (fmap∞ inj₂ Z)))))
 forcet (A□--∞ᵣᵣᵣ Z q x l m x₂) = A□p--ₛᵣᵣᵣᵣᵣ (forcep Z) x q l m (forcet x₂)


 A□--∞ᵣᵣᵣᵣ : {c₀ c₁ c₂ : Choice}(Z : Process∞ ∞ c₂)
         → (x   : ChoiceSet c₀)
         → (x₁  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  :  Tr∞ l m (fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x)) □+∞+ Z))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x)(fmap∞ inj₂ (addTimed✓∞  (inj₁ x₁) (fmap∞ inj₂ Z)))))
 forcet (A□--∞ᵣᵣᵣᵣ Z q x l m x₂) = A□p--ₛᵣᵣᵣᵣᵣ (forcep Z) x q l m (forcet x₂)


 A□--∞ᵣᵣᵣᵣᵣ : {c₀ c₁ c₂ : Choice}(Z : Process∞ ∞ c₂)
         → (x   : ChoiceSet c₀)
         → (q  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  :  Tr∞ l m (fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ q)) □+∞+ Z))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x)(fmap∞ inj₂ (addTimed✓∞  (inj₁ q) (fmap∞ inj₂ Z)))))
 forcet (A□--∞ᵣᵣᵣᵣᵣ Z q x l m x₂) = A□p--ₛᵣᵣᵣᵣᵣᵣ (forcep Z) x q l m (forcet x₂)

 A□--∞£ᵣᵣᵣᵣᵣᵣᵣᵣ : {c₀ c₁ c₂ : Choice}(Z : Process∞ ∞ c₂)
         → (x   : ChoiceSet c₀)
         → (x₁  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₂  : Tr∞ l m (fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x)) □+∞+ Z))
         →  Tr∞ l m (fmap∞ Ass⊎ᵣ (addTimed✓∞ (inj₁ x)(fmap∞ inj₂ (addTimed✓∞ (inj₁ x₁) (fmap∞ inj₂ ( Z))))))
 forcet (A□--∞£ᵣᵣᵣᵣᵣᵣᵣᵣ Z q x l m x₂) = A□p--ₛᵣᵣᵣᵣᵣᵣᵣᵣᵣ (forcep Z) x q l m (forcet x₂)

 A□p--ᵣᵣ : {c₀ c₁ c₂ : Choice}(P : Process ∞ c₀)
         → (x₁ : ChoiceSet c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₃  :  Tr l m ((addTimed✓ (inj₂ x) (fmap inj₁ (addTimed✓ (inj₂ x₁) (fmap inj₁ P))))))
         →  Tr l m (node (fmap+ Ass⊎ᵣ (P □p++ fmap+ unifyA⊎A (2-✓+ (inj₁ x₁) (inj₂ x)))))
 A□p--ᵣᵣ (terminate x) x₁ x₂ .[] .nothing (tnode empty) = tnode empty
 A□p--ᵣᵣ (terminate x) x₁ x₂ .(efq _ ∷ l) m (tnode (extc l .m () x₄))
 A□p--ᵣᵣ (terminate x) x₁ x₂ l m (tnode (intc .l .m () x₄))
 A□p--ᵣᵣ (terminate x) x₁ x₂ .[] .(just (inj₂ x₂)) (tnode (terc (inj₁ zero))) = tnode (terc (inj₂ (suc zero)))
 A□p--ᵣᵣ (terminate x) x₁ x₂ .[] .(just (inj₂ x₂)) (tnode (terc (inj₁ (suc ()))))
 A□p--ᵣᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₂ x₁))) (tnode (terc (inj₂ zero))) = tnode (terc (inj₂ zero))
 A□p--ᵣᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₁ x))) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₁ zero))
 A□p--ᵣᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (unifyA⊎A (if suc (suc _) then inj₁ (inj₂ x₁)
                                                          else (inj₂ (inj₁ x)))))) (tnode (terc (inj₂ (suc (suc ())))))
 A□p--ᵣᵣ (node x) x₁ x₂ l m x₃ = tnode (A□+--ᵣᵣ x m l x₁ x₂ x₃)


 A□p--ᵣᵣᵣ : {c₀ c₁ c₂ : Choice}(P : Process ∞ c₀)
         → (x₁ : ChoiceSet c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₃  :  Tr l m ((addTimed✓ (inj₂ x₁)(fmap inj₁ (addTimed✓ (inj₂ x) (fmap inj₁ P))))))
         →  Tr l m (node (fmap+ Ass⊎ᵣ (P □p++ fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x)))))
 A□p--ᵣᵣᵣ (terminate x) x₁ x₂ .[] .nothing (tnode empty) = tnode empty
 A□p--ᵣᵣᵣ (terminate x) x₁ x₂ .(efq _ ∷ l) m (tnode (extc l .m () x₄))
 A□p--ᵣᵣᵣ (terminate x) x₁ x₂ l m (tnode (intc .l .m () x₄))
 A□p--ᵣᵣᵣ (terminate x) x₁ x₂ .[] .(just (inj₂ x₁)) (tnode (terc (inj₁ zero))) = tnode (terc (inj₂ zero))
 A□p--ᵣᵣᵣ (terminate x) x₁ x₂ .[] .(just (inj₂ x₁)) (tnode (terc (inj₁ (suc x₃)))) = tnode (terc (inj₂ zero))
 A□p--ᵣᵣᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₂ x₂))) (tnode (terc (inj₂ zero))) = tnode (terc (inj₂ (suc zero)))
 A□p--ᵣᵣᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₁ x))) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₁  zero))
 A□p--ᵣᵣᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (unifyA⊎A (if suc (suc _) then inj₁ (inj₂ x₂)
                                                          else (inj₂ (inj₁ x)))))) (tnode (terc (inj₂ (suc (suc ())))))
 A□p--ᵣᵣᵣ (node x) x₁ x₂ l m x₃ = tnode (A□+--ᵣ x m l x₂ x₁ (forcet' l m x₃))



 A□p--ₛᵣ : {c₀ c₁ c₂ : Choice}(P : Process ∞ c₀)
         → (x₁ : ChoiceSet c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₃  : Tr l m (node (fmap+ Ass⊎ᵣ (P □p++ fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ x₁))))))
        →  Tr l m (node (fmap+ Ass⊎ᵣ (P □p++ fmap+ unifyA⊎A (2-✓+ (inj₂ x₁) (inj₁ x)))))
 A□p--ₛᵣ (terminate x) x₁ x₂ .[] .nothing (tnode empty) = tnode empty
 A□p--ₛᵣ (terminate x) x₁ x₂ .(efq _ ∷ l) m (tnode (extc l .m () x₄))
 A□p--ₛᵣ (terminate x) x₁ x₂ l m (tnode (intc .l .m () x₄))
 A□p--ₛᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₁ x))) (tnode (terc (inj₁ zero))) = tnode (terc (inj₁ zero))
 A□p--ₛᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₁ x))) (tnode (terc (inj₁ (suc x₃)))) = tnode (terc (inj₁ zero))
 A□p--ₛᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₂ x₂))) (tnode (terc (inj₂ zero))) = tnode (terc (inj₂ (suc zero)))
 A□p--ₛᵣ (terminate x) x₁ x₂ .[] .(just (inj₂ x₁)) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₂ zero))
 A□p--ₛᵣ (terminate x) x₁ x₂ .[] .(just (Ass⊎ᵣ (inj₂ (unifyA⊎A (if suc (suc _) then inj₁ (inj₁ x₂)
                                                                 else (inj₂ (inj₂ x₁))))))) (tnode (terc (inj₂ (suc (suc ())))))
 A□p--ₛᵣ (node x) x₁ x₂ l m (tnode x₃) = tnode (A□+--ₛᵣ x m l x₂ x₁ x₃)

 A□p--ₛᵣᵣᵣᵣ : {c₀ c₁ c₂ : Choice} (Z   : Process ∞ c₂)
         → (x   : ChoiceSet c₀)
         → (q   : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₃ : Tr l m (node (fmap+ unifyA⊎A (2-✓+ (inj₁ x) (inj₂ q)) □+p+ Z)))
        →  Tr l m (fmap Ass⊎ᵣ (addTimed✓ (inj₁ x)(fmap inj₂ (addTimed✓ (inj₁ q) (fmap inj₂ Z)))))
 A□p--ₛᵣᵣᵣᵣ (terminate x) x₁ q .[] .nothing (tnode empty) = tnode empty
 A□p--ₛᵣᵣᵣᵣ (terminate x) x₁ q .(efq _ ∷ l) m (tnode (extc l .m () x₃))
 A□p--ₛᵣᵣᵣᵣ (terminate x) x₁ q l m (tnode (intc .l .m () x₃))
 A□p--ₛᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₂ x)) (tnode (terc (inj₁ zero))) = tnode (terc (inj₂ (suc zero)))
 A□p--ₛᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₂ x)) (tnode (terc (inj₁ (suc x₂)))) = tnode (terc (inj₂ (suc zero)))
 A□p--ₛᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (inj₁ x₁))) (tnode (terc (inj₂ zero))) = tnode (terc (inj₁ zero))
 A□p--ₛᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (inj₂ q))) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₂ zero))
 A□p--ₛᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (unifyA⊎A (if suc (suc _) then inj₁ (inj₁ x₁)
                                                          else (inj₂ (inj₂ q)))))) (tnode (terc (inj₂ (suc (suc ())))))
 A□p--ₛᵣᵣᵣᵣ (node x) x₁ q l m (tnode x₂) = tnode (A□--+ᵣ x q x₁ l m x₂)


 A□p--ₛᵣᵣᵣᵣᵣ : {c₀ c₁ c₂ : Choice} (Z   : Process ∞ c₂)
         → (x   : ChoiceSet c₀)
         → (q   : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₃ : Tr l m (node (fmap+ unifyA⊎A (2-✓+ (inj₂ x) (inj₁ q)) □+p+ Z)))
        →  Tr l m (fmap Ass⊎ᵣ (addTimed✓ (inj₁ q)(fmap inj₂ (addTimed✓ (inj₁ x) (fmap inj₂ Z)))))
 A□p--ₛᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .nothing (tnode empty) = tnode empty
 A□p--ₛᵣᵣᵣᵣᵣ (terminate x) x₁ q .(efq _ ∷ l) m (tnode (extc l .m () x₃))
 A□p--ₛᵣᵣᵣᵣᵣ (terminate x) x₁ q l m (tnode (intc .l .m () x₃))
 A□p--ₛᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₂ x)) (tnode (terc (inj₁ zero))) = tnode (terc (inj₂ (suc zero)))
 A□p--ₛᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₂ x)) (tnode (terc (inj₁ (suc x₂)))) = tnode (terc (inj₂ (suc zero)))
 A□p--ₛᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (inj₂ x₁))) (tnode (terc (inj₂ zero))) = tnode (terc (inj₂ zero))
 A□p--ₛᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (inj₁ q))) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₁  zero))
 A□p--ₛᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (unifyA⊎A (if suc (suc _) then inj₁ (inj₂ x₁)
                                                           else (inj₂ (inj₁ q)))))) (tnode (terc (inj₂ (suc (suc ())))))
 A□p--ₛᵣᵣᵣᵣᵣ (node x) x₁ q l m x₃ = tnode (A□--+ᵣᵣ x x₁ q l m x₃)


 A□p--ₛᵣᵣᵣᵣᵣᵣ : {c₀ c₁ c₂ : Choice} (Z   : Process ∞ c₂)
         → (x   : ChoiceSet c₀)
         → (q   : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₃ :  Tr l m (node (fmap+ unifyA⊎A (2-✓+ (inj₁ q) (inj₂ x)) □+p+ Z)))
         →  Tr l m (fmap Ass⊎ᵣ (addTimed✓ (inj₁ q)(fmap inj₂ (addTimed✓ (inj₁ x) (fmap inj₂ Z)))))
 A□p--ₛᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .nothing (tnode empty) = tnode empty
 A□p--ₛᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .(efq _ ∷ l) m (tnode (extc l .m () x₃))
 A□p--ₛᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q l m (tnode (intc .l .m () x₃))
 A□p--ₛᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₂ x)) (tnode (terc (inj₁ zero))) = tnode (terc (inj₂ (suc zero)))
 A□p--ₛᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₂ x)) (tnode (terc (inj₁ (suc x₂)))) = tnode (terc (inj₂ (suc zero)))
 A□p--ₛᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (inj₁ q))) (tnode (terc (inj₂ zero))) = tnode (terc (inj₁ zero))
 A□p--ₛᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (inj₂ x₁))) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₂ zero))
 A□p--ₛᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (unifyA⊎A (if suc (suc _) then inj₁ (inj₁ q)
                                                           else (inj₂ (inj₂ x₁)))))) (tnode (terc (inj₂ (suc (suc ())))))
 A□p--ₛᵣᵣᵣᵣᵣᵣ (node x) x₁ q l m x₂ = tnode (A□--+ᵣᵣᵣᵣ x x₁ q l m x₂)

 A□p--ₛᵣᵣᵣᵣᵣᵣᵣᵣᵣ : {c₀ c₁ c₂ : Choice} (Z : Process ∞ c₂)
         → (x   : ChoiceSet c₁)
         → (q   : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → (x₃ :  Tr l m (node (fmap+ unifyA⊎A (2-✓+ (inj₂ x) (inj₁ q)) □+p+ Z)))
         →  Tr l m (fmap Ass⊎ᵣ (addTimed✓ (inj₁ q)(fmap inj₂ (addTimed✓ (inj₁ x) (fmap inj₂ Z)))))
 A□p--ₛᵣᵣᵣᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .nothing (tnode empty) = tnode empty
 A□p--ₛᵣᵣᵣᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .(efq _ ∷ l) m (tnode (extc l .m () x₃))
 A□p--ₛᵣᵣᵣᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q l m (tnode (intc .l .m () x₃))
 A□p--ₛᵣᵣᵣᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₂ x)) (tnode (terc (inj₁ zero))) = tnode (terc (inj₂ (suc zero)))
 A□p--ₛᵣᵣᵣᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₂ x)) (tnode (terc (inj₁ (suc x₂)))) = tnode (terc (inj₂ (suc zero)))
 A□p--ₛᵣᵣᵣᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (inj₂ x₁))) (tnode (terc (inj₂ zero))) = tnode (terc (inj₂ zero))
 A□p--ₛᵣᵣᵣᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (inj₁ q))) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₁ zero))
 A□p--ₛᵣᵣᵣᵣᵣᵣᵣᵣᵣ (terminate x) x₁ q .[] .(just (inj₁ (unifyA⊎A (if suc (suc _) then inj₁ (inj₂ x₁)
                                                            else (inj₂ (inj₁ q)))))) (tnode (terc (inj₂ (suc (suc ())))))
 A□p--ₛᵣᵣᵣᵣᵣᵣᵣᵣᵣ (node x) x₁ q l m x₃ = A□--+ₛᵣᵣ x q x₁ l m (forcet' l m x₃)


 A□-p-ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process ∞ c₁)
         → (x₁ : ChoiceSet c₀)
         → (x  : ChoiceSet c₂)
         → (l  : List Label)
         → (m  : Maybe maybeExtC)
         → ( x₃  : Tr l m (addTimed✓ (inj₂ x₁) (fmap inj₁ (addTimed✓ (inj₁ x) (fmap inj₂ ( Q))))))
         →  Tr l m (fmap Ass⊎ᵣ (addTimed✓ (inj₁ x) (fmap inj₂ (addTimed✓ (inj₂ x₁) (fmap inj₁ Q)))))
 A□-p-ᵣ (terminate x) x₁ x₂ .[] .nothing (tnode empty) = tnode empty
 A□-p-ᵣ (terminate x) x₁ x₂ .(efq _ ∷ l) m (tnode (extc l .m () x₄))
 A□-p-ᵣ (terminate x) x₁ x₂ l m (tnode (intc .l .m () x₄))
 A□-p-ᵣ (terminate x) x₁ x₂ .[] .(just (inj₂ x₁)) (tnode (terc (inj₁ zero))) = tnode (terc (inj₂ zero))
 A□-p-ᵣ (terminate x) x₁ x₂ .[] .(just (inj₂ x₁)) (tnode (terc (inj₁ (suc x₃)))) = tnode (terc (inj₂ zero))
 A□-p-ᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₁ x₂))) (tnode (terc (inj₂ zero))) = tnode (terc (inj₁  zero))
 A□-p-ᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (inj₂ x))) (tnode (terc (inj₂ (suc zero)))) = tnode (terc (inj₂ (suc zero)))
 A□-p-ᵣ (terminate x) x₁ x₂ .[] .(just (inj₁ (unifyA⊎A (if suc (suc _) then inj₁ (inj₁ x₂)
                                                         else (inj₂ (inj₂ x)))))) (tnode (terc (inj₂ (suc (suc ())))))
 A□-p-ᵣ (node x) x₁ x₂ l m (tnode x₃) = tnode (A□-+-ᵣ x x₁ x₂ l m x₃)









≡A□+ : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁)  (Z : Process+ ∞ c₂)
        → ((P □++ Q) □++ Z) ≡+  fmap+ Ass⊎ᵣ (P □++ (Q  □++ Z ))
≡A□+ P Q Z = (A□+ P Q Z) , A□+ᵣ P Q Z



