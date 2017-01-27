module proofAssInterleaving where 

open import process
open import TraceWithoutSize
open Tr∞
open import Size
open import choiceSetU
open import auxData
open import Data.Maybe
open import Data.Product
open import interleave
open import Data.List
open import Data.Sum
open import label
open import renamingResult
open import RefWithoutSize
open import dataAuxFunction
open import lemFmap
open import traceEquivalence
open import Data.Product


maybeChoice : {c₀ c₁ c₂ : Choice} → Set
maybeChoice {c₀} {c₁} {c₂} = ((ChoiceSet c₀ auxData.× ChoiceSet c₁) auxData.× ChoiceSet c₂)



mutual 
 S|||+ : {c₀ c₁ c₂ : Choice}  (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁) (Z : Process+ ∞ c₂)
        →  ((P |||++ Q) |||++ Z) ⊑+ fmap+ Ass× (P |||++ (Q  |||++ Z ))
 S|||+ P Q Z .[] .nothing empty = empty
 S|||+ P Q Z .(Lab P x ∷ l) m (extc l .m (inj₁ x) x₁)        = extc l m (inj₁ (inj₁ x)) (S|||∞++ (PE P x) Q Z l m x₁)
 S|||+ P Q Z .(Lab Q x ∷ l) m (extc l .m (inj₂ (inj₁ x)) x₁) = extc l m (inj₁ (inj₂ x)) (S|||+∞+ P (PE Q x) Z l m x₁)
 S|||+ P Q Z .(Lab Z y ∷ l) m (extc l .m (inj₂ (inj₂ y)) x₁) = extc l m (inj₂ y)        (S|||++∞ P Q (PE Z y) l m x₁)
 S|||+ P Q Z l m (intc .l .m (inj₁ x) x₁)                    = intc l m (inj₁ (inj₁ x)) (S|||∞++ (PI P x) Q Z l m x₁)
 S|||+ P Q Z l m (intc .l .m (inj₂ (inj₁ x)) x₁)             = intc l m (inj₁ (inj₂ x)) (S|||+∞+ P (PI Q x) Z l m x₁)
 S|||+ P Q Z l m (intc .l .m (inj₂ (inj₂ y)) x₁)             = intc l m (inj₂ y)        (S|||++∞ P Q (PI Z y) l m x₁)
 S|||+ P Q Z .[] .(just ((PT P x ,, PT Q x₁) ,, PT Z x₂)) (terc (x ,, (x₁ ,, x₂))) = terc ((x ,, x₁) ,, x₂)

 S|||∞++ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                              (Q : Process+ ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → Ref∞  (((P |||∞+ Q) |||∞+ Z)) (fmap∞ Ass× ( P |||∞+ (Q |||++ Z)))
 forcet (S|||∞++ P Q Z l m x) = tnode (S|||+pp (forcep P) Q Z l m (forcet' l m (forcet x)))

 S|||+∞+ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process∞ ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → Ref∞ (((P |||+∞ Q) |||∞+ Z)) (fmap∞ Ass× ( P |||+∞ (Q |||∞+ Z)))
 forcet (S|||+∞+ P Q Z l m x) = tnode (S|||p+p P (forcep Q) Z l m (forcet' l m (forcet x)))

 S|||++∞  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                               (Q : Process+ ∞ c₁)
                               (Z : Process∞ ∞ c₂)
         → Ref∞ (((P |||++ Q) |||+∞ Z)) (fmap∞ Ass× ( P |||+∞ (Q |||+∞ Z)))
 forcet (S|||++∞ P Q Z l m x)  = tnode (S|||pp+ P Q (forcep Z) l m (forcet' l m (forcet x)))


 S|||+pp  : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                               (Q : Process+ ∞ c₁)
                               (Z : Process+ ∞ c₂)
         →  Ref+ (((P |||p+ Q) |||++ Z)) (fmap+ Ass× ( P |||p+ (Q |||++ Z)))
 S|||+pp (terminate x) Q Z l m tr = S|||-++ Q Z x l m tr
 S|||+pp (node x) Q Z l m tr      = S|||+ x Q Z l m tr


 S|||p+p : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process  ∞ c₁)
                              (Z : Process+ ∞ c₂)
         →  Ref+  (((P |||+p Q) |||++ Z)) (fmap+ Ass× ( P |||++ (Q |||p+ Z)))
 S|||p+p P (terminate x) Z l m tr = S|||+-+ P Z x l m tr
 S|||p+p P (node x) Z l m tr      = S|||+ P x Z l m tr


 S|||pp+ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process+ ∞ c₁)
                              (Z : Process  ∞ c₂)
         →  Ref+ (((P |||++ Q) |||+p Z)) (fmap+ Ass× ( P |||++ (Q |||+p Z)))
 S|||pp+ P Q (terminate x) l m tr = S|||++- P Q m l x tr
 S|||pp+ P Q (node x) l m tr      = S|||+ P Q x  l m tr



 S|||-++ : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → (x : ChoiceSet c₀)
         → (l : List Label)
         → (m : Maybe maybeChoice)
         → (x₂  : Tr+ l m (fmap+ Ass× (fmap+ (_,,_ x) (Q |||++ Z))))
         →  Tr+ l m (fmap+ (_,,_ x) Q |||++ Z)
 S|||-++ Q Z x .[] .nothing empty = empty
 S|||-++ Q Z x .(Lab Q x₁ ∷ l) m (extc l .m (inj₁ x₁) x₂) = extc l m (inj₁ x₁) (S|||-∞+ (PE Q x₁) Z x l m x₂)
 S|||-++ Q Z x .(Lab Z y ∷ l) m (extc l .m (inj₂ y) x₂)   = extc l m (inj₂ y ) (S|||-+∞  Q (PE Z y) x l m x₂)
 S|||-++ Q Z x l m (intc .l .m (inj₁ x₁) x₂)              = intc l m (inj₁ x₁) (S|||-∞+ (PI Q x₁) Z x l m x₂)
 S|||-++ Q Z x l m (intc .l .m (inj₂ y) x₂)               = intc l m (inj₂ y ) (S|||-+∞  Q (PI Z y) x l m x₂)
 S|||-++ Q Z x .[] .(just ((x ,, PT Q x₁) ,, PT Z x₂)) (terc (x₁ ,, x₂)) = terc (x₁ ,, x₂)        



 S|||+-+ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (tr : Tr+ l m (fmap+ Ass× (P |||++ fmap+ (_,,_ x) Z)))
         →  Tr+ l m (fmap+ (λ a → a ,, x) P |||++ Z)
 S|||+-+ P Z x .[] .nothing empty                         = empty
 S|||+-+ P Z x .(Lab P x₁ ∷ l) m (extc l .m (inj₁ x₁) x₂) = extc l m (inj₁ x₁)(S|||∞-+ (PE P x₁) Z x l m x₂)
 S|||+-+ P Z x .(Lab Z y  ∷ l) m (extc l .m (inj₂ y) x₂)  = extc l m (inj₂ y) (S|||+-∞  P (PE Z y) x l m x₂)
 S|||+-+ P Z x l m (intc .l .m (inj₁ x₁) x₂)              = intc l m (inj₁ x₁)(S|||∞-+ (PI P x₁) Z x l m x₂)
 S|||+-+ P Z x l m (intc .l .m (inj₂ y) x₂)               = intc l m (inj₂ y) (S|||+-∞  P (PI Z y) x l m x₂)
 S|||+-+ P Z x .[] .(just ((PT P x₁ ,, x) ,, PT Z x₂)) (terc (x₁ ,, x₂)) = terc (x₁ ,, x₂)


 S|||++- : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (tr : Tr+ l m (fmap+ Ass× (P |||++ fmap+ (λ a → a ,, x) Q)))
         →  Tr+ l m (fmap+ (λ a → a ,, x) (P |||++ Q))
 S|||++- P Q .nothing .[] x empty = empty
 S|||++- P Q m .(Lab P x₁ ∷ l) x (extc l .m (inj₁ x₁) x₂) = extc l m (inj₁ x₁) (S|||∞+- (PE P x₁) Q m l x x₂)
 S|||++- P Q m .(Lab Q y ∷ l)  x (extc l .m (inj₂ y) x₂)  = extc l m (inj₂ y)  (S|||+∞-  P (PE Q y) m l x x₂)
 S|||++- P Q m l x (intc .l .m (inj₁ x₁) x₂)              = intc l m (inj₁ x₁) (S|||∞+- (PI P x₁) Q m l x x₂)
 S|||++- P Q m l x (intc .l .m (inj₂ y) x₂)               = intc l m (inj₂ y)  (S|||+∞-  P (PI Q y) m l x x₂)
 S|||++- P Q .(just ((PT P x₁ ,, PT Q x₂) ,, x)) .[] x (terc (x₁ ,, x₂)) = terc (x₁ ,, x₂)



 S|||-∞+ : {c₀ c₁ c₂ : Choice}(Q : Process∞ ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ : Tr∞ l m (fmap∞ Ass× (fmap∞ (_,,_ x) (Q |||∞+ Z))))
         → Tr∞ l m (fmap∞ (_,,_ x) Q |||∞+ Z)
 forcet (S|||-∞+ Q Z x l m tr) = tnode (S|||-p+ (forcep Q) Z x l m (forcet' l m (forcet tr)))


 S|||∞-+ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ : Tr∞ l m (fmap∞ Ass× ( P |||∞+ fmap+ (_,,_ x) Z)))
         → Tr∞ l m (fmap∞ (λ a → a ,, x) P |||∞+ Z)
 forcet (S|||∞-+ P Z x l m x₂) = S|||p-+ (forcep P) Z x l m (forcet' l m (forcet x₂))


 S|||∞+- : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                              (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂ : Tr∞ l m (fmap∞ Ass× ( P |||∞+ fmap+ (λ a → a ,, x) Q)))
         → Tr∞ l m (fmap∞ (λ a → a ,, x) ( P |||∞+ Q))
 forcet (S|||∞+- P Q m l x x₂) = tnode (S|||p+- (forcep P) Q m l x (forcet' l m (forcet x₂)))


 S|||+∞-  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                               (Q : Process∞ ∞ c₁)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂ : Tr∞ l m (fmap∞ Ass× (P |||+∞ fmap∞ (λ a → a ,, x) Q )))
         → Tr∞ l m (fmap∞ (λ a → a ,, x) (P |||+∞ Q ))
 forcet (S|||+∞- P Q m l x x₂) = tnode (S|||+p- P (forcep Q) m l x (forcet' l m (forcet x₂))) 


 S|||+-∞  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                               (Z : Process∞ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ : Tr∞ l m (fmap∞ Ass× (P |||+∞ fmap∞ (_,,_ x) (Z))))
         → Tr∞ l m (fmap+ (λ a → a ,, x) P |||+∞ Z)
 forcet (S|||+-∞  P Z x l m x₂) = tnode (S|||+-p  P (forcep Z) x l m (forcet' l m (forcet x₂)))


 S|||-+∞  : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                               (Z : Process∞ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ : Tr∞ l m (fmap∞ Ass× (fmap∞ (_,,_ x) (Q |||+∞ Z ))))
         → Tr∞ l m (fmap+ (_,,_ x) Q |||+∞ Z) 
 forcet (S|||-+∞  Q Z x l m tr) = tnode (S|||-+p Q (forcep Z) x l m (forcet' l m (forcet tr)))


 S|||-p+ : {c₀ c₁ c₂ : Choice}(Q : Process  ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ : Tr+ l m (fmap+ Ass× (fmap+ (_,,_ x)(Q |||p+ Z))))
         → Tr+ l m (fmap (_,,_ x)  Q |||p+ Z)
 S|||-p+ (terminate q) Z x l m tr = S|||--+  Z q x l m tr
 S|||-p+ (node q) Z x l m tr      = S|||-++ q Z x l m tr


 S|||+-p  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                               (Z : Process  ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ : Tr+ l m (fmap+ Ass× (P |||+p fmap (_,,_ x) Z)))
         →  Tr+ l m (fmap+ (λ a → a ,, x) P |||+p Z) 
 S|||+-p  P (terminate x) x₁ l m x₂ = S|||+-- P m l x₁ x x₂
 S|||+-p  P (node x) x₁ l m x₂      = S|||+-+ P x x₁ l m x₂ 

 S|||+p- : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process  ∞ c₁)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂ : Tr+ l m (fmap+ Ass× (P |||+p fmap (λ a → a ,, x) Q)))
         →  Tr+ l m (fmap+ (λ a → a ,, x) (P |||+p Q))
 S|||+p- P (terminate x) m l x₁ x₂ = S|||+-- P m l x x₁ x₂
 S|||+p- P (node x) m l x₁ x₂      = S|||++- P x m l x₁ x₂ 


 S|||p+- : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                              (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂ : Tr+ l m (fmap+ Ass× (P |||p+ fmap+ (λ a → a ,, x) Q)))
         →  Tr+ l m (fmap+ (λ a → a ,, x) ( P |||p+ Q))
 S|||p+- (terminate x) Q m l x₁ x₂ = S|||-+- Q x x₁ l m x₂
 S|||p+- (node x) Q m l x₁ x₂      = S|||++- x Q m l x₁ x₂


 S|||p-+ : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ : Tr+ l m (fmap+ Ass× (P |||p+ fmap+ (_,,_ x) Z)))
         → Tr l m (node (fmap (λ a → a ,, x) ( P) |||p+ Z))
 S|||p-+ (terminate x) Z x₁ l m x₂ = tnode (S|||--+ Z x₁ x l m x₂)
 S|||p-+ (node x) Z x₁ l m x₂      = tnode (S|||+-+ x Z x₁ l m x₂)


 S|||-+p : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                              (Z : Process  ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeChoice) 
         → (x₂ : Tr+ l m (fmap+ Ass× (fmap+ (_,,_ x) (Q |||+p Z ))))
         → Tr+ l m (fmap+ (_,,_ x) Q |||+p Z) 
 S|||-+p Q (terminate x) x₁ l m tr = S|||-+- Q x₁ x l m tr
 S|||-+p Q (node x) x₁ l m tr      = S|||-++ Q x x₁ l m tr


 S|||+-- : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → (x₂ : Tr+ l m (fmap+ Ass× (fmap+ (λ a → a ,, (x ,, x₁)) P)))
         →  Tr+ l m (fmap+ (λ a → a ,, x₁) (fmap+ (λ a → a ,, x) P))
 S|||+-- P .nothing .[] x x₁ empty                           = empty
 S|||+-- P m .(Lab P x₂ ∷ l) x x₁ (extc l .m x₂ x₃)          = extc l m x₂ (S|||∞-- (PE P x₂) m l x x₁ x₃)
 S|||+-- P m l x x₁ (intc .l .m x₂ x₃)                       = intc l m x₂ (S|||∞-- (PI P x₂) m l x x₁ x₃)
 S|||+-- P .(just ((PT P x₂ ,, x) ,, x₁)) .[] x x₁ (terc x₂) = terc x₂


 S|||∞-- : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → (x₃ : Tr∞ l m (fmap∞ Ass× (fmap∞ (λ a → a ,, (x ,, x₁)) P)))
         → Tr∞ l m (fmap∞ (λ a → a ,, x₁) (fmap∞ (λ a → a ,, x) P ))
 forcet (S|||∞-- P m l x x₁ x₃) =  S|||p-- (forcep P) x x₁ l m (forcet x₃)


 S|||--+  : {c₀ c₁ c₂ : Choice}(Z : Process+ ∞ c₂)
         → (q   : ChoiceSet c₁)
         → (x   : ChoiceSet c₀)
         → (l : List Label)
         → (m : Maybe maybeChoice)
         → (tr  : Tr+ l m (fmap+ Ass× (fmap+ (_,,_ x) (fmap+ (_,,_ q) Z))))
         → Tr+ l m (fmap+ (_,,_ (x ,, q)) Z)
 S|||--+  Z q x .[] .nothing empty                          = empty
 S|||--+  Z q x .(Lab Z x₁ ∷ l) m (extc l .m x₁ x₂)         = extc l m x₁ (S|||--∞ (PE Z x₁) q x l m x₂)
 S|||--+  Z q x l m (intc .l .m x₁ x₂)                      = intc l m x₁ (S|||--∞ (PI Z x₁) q x l m x₂)
 S|||--+  Z q x .[] .(just ((x ,, q) ,, PT Z x₁)) (terc x₁) = (terc x₁)


 S|||-+- : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
         → (x₁ : ChoiceSet c₀)
         → (x  : ChoiceSet c₂)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (tr : Tr+ l m (fmap+ Ass× (fmap+ (_,,_ x₁) (fmap+ (λ a → a ,, x) Q))))
         → Tr+ l m (fmap+ (λ a → a ,, x) (fmap+ (_,,_ x₁) Q))
 S|||-+- Q x₁ x .[] .nothing empty                           = empty
 S|||-+- Q x₁ x .(Lab Q x₂ ∷ l) m (extc l .m x₂ x₃)          = extc l m x₂ (S|||-∞- (PE Q x₂) m l x₁ x x₃)
 S|||-+- Q x₁ x l m (intc .l .m x₂ x₃)                       = intc l m x₂ (S|||-∞- (PI Q x₂) m l x₁ x x₃)
 S|||-+- Q x₁ x .[] .(just ((x₁ ,, PT Q x₂) ,, x)) (terc x₂) = (terc x₂)



 S|||--∞ : {c₀ c₁ c₂ : Choice}(Z : Process∞ ∞ c₂)
         → (q  : ChoiceSet c₁)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ : Tr∞ l m (fmap∞ Ass× (fmap∞ (_,,_ x) (fmap∞ (_,,_ q) Z ))))
         → Tr∞ l m (fmap∞ (_,,_ (x ,, q)) Z )
 forcet (S|||--∞ Z q x l m x₂) = S|||--p (forcep Z) x q l m (forcet x₂)



 S|||-∞- : {c₀ c₁ c₂ : Choice}(Q : Process∞ ∞ c₁)
         → (m  : Maybe ((ChoiceSet c₀ auxData.× ChoiceSet c₁) auxData.× ChoiceSet c₂))
         → (l  : List Label)
         → (x  : ChoiceSet c₀)
         → (x₁ : ChoiceSet c₂)
         → (x₃ : Tr∞ l m (fmap∞ Ass× (fmap∞ (_,,_ x) (fmap∞ (λ a → a ,, x₁) Q))))
         → Tr∞ l m (fmap∞ (λ a → a ,, x₁) (fmap∞ (_,,_ x) Q))
 forcet (S|||-∞- Q m l x x₁ x₃) =  S|||-p- (forcep Q) x x₁ l m (forcet x₃)


 S|||--p : {c₀ c₁ c₂ : Choice}(Z : Process ∞ c₂)
         → (x : ChoiceSet c₀)
         → (q : ChoiceSet c₁)
         → (l : List Label)
         → (m : Maybe maybeChoice)
         → (x₂  : Tr l m (fmap Ass× (fmap (_,,_ x)(fmap (_,,_ q) Z) )))
         → Tr l m (fmap (_,,_ (x ,, q)) Z)
 S|||--p (terminate x) x₁ q l m x₂ = lemFmap (λ x₃ → x) ((_,,_ (x₁ ,, q))) (terminate (x)) l m x₂
 S|||--p (node x)      x₁ q l m x₂ = tnode (S|||--+ x q x₁ l m (forcet' l m x₂))

 S|||-p- : {c₀ c₁ c₂ : Choice}(Q : Process ∞ c₁)
         → (x₁ : ChoiceSet c₀)
         → (x  : ChoiceSet c₂)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₃ : Tr l m (fmap Ass× (fmap (_,,_ x₁) (fmap (λ a → a ,, x) Q))))
         → Tr l m (fmap (λ a → a ,, x) (fmap (_,,_ x₁) (Q)))
 S|||-p- (terminate x) x₁ x₂ l m x₃ = lemFmap ((λ x₃ → x)) (λ x₄ → (x₁ ,, x) ,, x₂) (terminate (x)) l m x₃
 S|||-p- (node x)      x₁ x₂ l m x₃ = tnode (S|||-+- x x₁ x₂ l m (forcet' l m x₃)) 


 S|||p-- : {c₀ c₁ c₂ : Choice}(P : Process ∞ c₀)
         → (x₁ : ChoiceSet c₁)
         → (x  : ChoiceSet c₂)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₃ : Tr l m (fmap Ass× (fmap (λ a → a ,, (x₁ ,, x)) P)))
         → Tr l m (fmap (λ a → a ,, x) (fmap (λ a → a ,, x₁) P))
 S|||p-- (terminate x) x₁ x₂ l m x₃ = lemFmap (λ x₄ → x) (λ x₄ → (x ,, x₁) ,, x₂) (terminate (x)) l m x₃
 S|||p-- (node x)      x₁ x₂ l m x₃ = tnode (S|||+-- x m l x₁ x₂ (forcet' l m x₃))












mutual 
 S|||+ᵣ : {c₀ c₁ c₂ : Choice}  (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁) (Z : Process+ ∞ c₂)
        →  fmap+ Ass× (P |||++ (Q  |||++ Z )) ⊑+ ((P |||++ Q) |||++ Z)
 S|||+ᵣ P Q Z .[] .nothing empty = empty
 S|||+ᵣ P Q Z .(Lab P x ∷ l) m (extc l .m (inj₁ (inj₁ x)) x₁) = extc l m (inj₁ x)        (S|||∞++ᵣ (PE P x) Q Z l m x₁)
 S|||+ᵣ P Q Z .(Lab Q y ∷ l) m (extc l .m (inj₁ (inj₂ y)) x₁) = extc l m (inj₂ (inj₁ y)) (S|||+∞+ᵣ P (PE Q y) Z l m x₁)
 S|||+ᵣ P Q Z .(Lab Z y ∷ l) m (extc l .m (inj₂ y) x₁)        = extc l m (inj₂ (inj₂ y)) (S|||++∞ᵣ P Q (PE Z y) l m x₁)
 S|||+ᵣ P Q Z l m (intc .l .m (inj₁ (inj₁ x)) x₁)             = intc l m (inj₁ x)        (S|||∞++ᵣ (PI P x) Q Z l m x₁)
 S|||+ᵣ P Q Z l m (intc .l .m (inj₁ (inj₂ y)) x₁)             = intc l m (inj₂ (inj₁ y)) (S|||+∞+ᵣ P (PI Q y) Z l m x₁)
 S|||+ᵣ P Q Z l m (intc .l .m (inj₂ y) x₁)                    = intc l m (inj₂ (inj₂ y)) (S|||++∞ᵣ P Q (PI Z y) l m x₁)
 S|||+ᵣ P Q Z .[] .(just ((PT P x ,, PT Q x₁) ,, PT Z x₂)) (terc ((x ,, x₁) ,, x₂)) = terc (x ,, (x₁ ,, x₂))

 S|||∞++ᵣ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                              (Q : Process+ ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → Ref∞  (fmap∞ Ass× ( P |||∞+ (Q |||++ Z))) (((P |||∞+ Q) |||∞+ Z))
 forcet (S|||∞++ᵣ P Q Z l m x) = tnode (S|||+ppᵣ (forcep P) Q Z l m (forcet' l m (forcet x)))

 S|||+∞+ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process∞ ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → Ref∞  (fmap∞ Ass× ( P |||+∞ (Q |||∞+ Z))) (((P |||+∞ Q) |||∞+ Z))
 forcet (S|||+∞+ᵣ P Q Z l m x) = tnode (S|||p+pᵣ P (forcep Q) Z l m (forcet' l m (forcet x)))

 S|||++∞ᵣ  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                               (Q : Process+ ∞ c₁)
                               (Z : Process∞ ∞ c₂)
         → Ref∞  (fmap∞ Ass× ( P |||+∞ (Q |||+∞ Z))) (((P |||++ Q) |||+∞ Z))
 forcet (S|||++∞ᵣ P Q Z l m x)  = tnode (S|||pp+ᵣ P Q (forcep Z) l m (forcet' l m (forcet x)))



 S|||+ppᵣ  : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                               (Q : Process+ ∞ c₁)
                               (Z : Process+ ∞ c₂)
         →  Ref+ (fmap+ Ass× ( P |||p+ (Q |||++ Z))) (((P |||p+ Q) |||++ Z))
 S|||+ppᵣ (terminate x) Q Z l m tr = S|||-++ᵣ Q Z x l m tr
 S|||+ppᵣ (node x) Q Z l m tr      = S|||+ᵣ x Q Z l m tr


 S|||p+pᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process  ∞ c₁)
                              (Z : Process+ ∞ c₂)
         →  Ref+  (fmap+ Ass× ( P |||++ (Q |||p+ Z))) (((P |||+p Q) |||++ Z))
 S|||p+pᵣ P (terminate x) Z l m tr = S|||+-+ᵣ P Z x l m tr
 S|||p+pᵣ P (node x) Z l m tr      = S|||+ᵣ P x Z l m tr


 S|||pp+ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process+ ∞ c₁)
                              (Z : Process  ∞ c₂)
         →  Ref+ (fmap+ Ass× ( P |||++ (Q |||+p Z))) (((P |||++ Q) |||+p Z))
 S|||pp+ᵣ P Q (terminate x) l m tr = S|||++-ᵣ P Q m l x tr
 S|||pp+ᵣ P Q (node x) l m tr      = S|||+ᵣ P Q x  l m tr



 S|||-++ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → (x : ChoiceSet c₀)
         → (l : List Label)
         → (m : Maybe maybeChoice)
         → (x₂  : Tr+ l m (fmap+ (_,,_ x) Q |||++ Z))
         →  Tr+ l m (fmap+ Ass× (fmap+ (_,,_ x) (Q |||++ Z)))
 S|||-++ᵣ Q Z x .[] .nothing empty = empty
 S|||-++ᵣ Q Z x .(Lab Q x₁ ∷ l) m (extc l .m (inj₁ x₁) x₂) =  extc l m (inj₁ x₁) (S|||-∞+ᵣ (PE Q x₁) Z x l m x₂)
 S|||-++ᵣ Q Z x .(Lab Z y ∷ l) m (extc l .m (inj₂ y) x₂)   =  extc l m (inj₂ y ) (S|||-+∞ᵣ  Q (PE Z y) x l m x₂)
 S|||-++ᵣ Q Z x l m (intc .l .m (inj₁ x₁) x₂)              =  intc l m (inj₁ x₁) (S|||-∞+ᵣ (PI Q x₁) Z x l m x₂)
 S|||-++ᵣ Q Z x l m (intc .l .m (inj₂ y) x₂)               =  intc l m (inj₂ y ) (S|||-+∞ᵣ  Q (PI Z y) x l m x₂)
 S|||-++ᵣ Q Z x .[] .(just ((x ,, PT Q x₁) ,, PT Z x₂)) (terc (x₁ ,, x₂)) = terc (x₁ ,, x₂)        

 S|||+-+ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (tr : Tr+ l m (fmap+ (λ a → a ,, x) P |||++ Z))
         →  Tr+ l m (fmap+ Ass× (P |||++ fmap+ (_,,_ x) Z))
 S|||+-+ᵣ P Z x .[] .nothing empty                         = empty
 S|||+-+ᵣ P Z x .(Lab P x₁ ∷ l) m (extc l .m (inj₁ x₁) x₂) = extc l m (inj₁ x₁)(S|||∞-+ᵣ (PE P x₁) Z x l m x₂)
 S|||+-+ᵣ P Z x .(Lab Z y  ∷ l) m (extc l .m (inj₂ y) x₂)  = extc l m (inj₂ y) (S|||+-∞ᵣ  P (PE Z y) x l m x₂)
 S|||+-+ᵣ P Z x l m (intc .l .m (inj₁ x₁) x₂)              = intc l m (inj₁ x₁)(S|||∞-+ᵣ (PI P x₁) Z x l m x₂)
 S|||+-+ᵣ P Z x l m (intc .l .m (inj₂ y) x₂)               = intc l m (inj₂ y) (S|||+-∞ᵣ  P (PI Z y) x l m x₂)
 S|||+-+ᵣ P Z x .[] .(just ((PT P x₁ ,, x) ,, PT Z x₂)) (terc (x₁ ,, x₂)) = terc (x₁ ,, x₂)


 S|||++-ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (tr :  Tr+ l m (fmap+ (λ a → a ,, x) (P |||++ Q)))
         →  Tr+ l m (fmap+ Ass× (P |||++ fmap+ (λ a → a ,, x) Q))
 S|||++-ᵣ P Q .nothing .[] x empty = empty
 S|||++-ᵣ P Q m .(Lab P x₁ ∷ l) x (extc l .m (inj₁ x₁) x₂) =  extc l m (inj₁ x₁) (S|||∞+-ᵣ (PE P x₁) Q m l x x₂)
 S|||++-ᵣ P Q m .(Lab Q y ∷ l)  x (extc l .m (inj₂ y) x₂)  =  extc l m (inj₂ y)  (S|||+∞-ᵣ  P (PE Q y) m l x x₂)
 S|||++-ᵣ P Q m l x (intc .l .m (inj₁ x₁) x₂)              =  intc l m (inj₁ x₁) (S|||∞+-ᵣ (PI P x₁) Q m l x x₂)
 S|||++-ᵣ P Q m l x (intc .l .m (inj₂ y) x₂)               =  intc l m (inj₂ y)  (S|||+∞-ᵣ  P (PI Q y) m l x x₂)
 S|||++-ᵣ P Q .(just ((PT P x₁ ,, PT Q x₂) ,, x)) .[] x (terc (x₁ ,, x₂)) = terc (x₁ ,, x₂)



 S|||-∞+ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process∞ ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ :  Tr∞ l m (fmap∞ (_,,_ x) Q |||∞+ Z))
         →  Tr∞ l m (fmap∞ Ass× (fmap∞ (_,,_ x) (Q |||∞+ Z)))
 forcet (S|||-∞+ᵣ Q Z x l m tr) = tnode (S|||-p+ᵣ (forcep Q) Z x l m (forcet' l m (forcet tr)))


 S|||∞-+ᵣ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ :  Tr∞ l m (fmap∞ (λ a → a ,, x) P |||∞+ Z))
         →  Tr∞ l m (fmap∞ Ass× ( P |||∞+ fmap+ (_,,_ x) Z))
 forcet (S|||∞-+ᵣ P Z x l m x₂) = tnode (S|||p-+ᵣ (forcep P) Z x l m (forcet x₂))


 S|||∞+-ᵣ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
                              (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂ :  Tr∞ l m (fmap∞ (λ a → a ,, x) ( P |||∞+ Q)))
         →  Tr∞ l m (fmap∞ Ass× ( P |||∞+ fmap+ (λ a → a ,, x) Q))
 forcet (S|||∞+-ᵣ P Q m l x x₂) = tnode (S|||p+-ᵣ (forcep P) Q m l x (forcet' l m (forcet x₂)))


 S|||+∞-ᵣ  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                               (Q : Process∞ ∞ c₁)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂ :  Tr∞ l m (fmap∞ (λ a → a ,, x) (P |||+∞ Q )))
         →  Tr∞ l m (fmap∞ Ass× (P |||+∞ fmap∞ (λ a → a ,, x) Q ))
 forcet (S|||+∞-ᵣ P Q m l x x₂) = tnode (S|||+p-ᵣ P (forcep Q) m l x (forcet' l m (forcet x₂))) 


 S|||+-∞ᵣ  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                               (Z : Process∞ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ :  Tr∞ l m (fmap+ (λ a → a ,, x) P |||+∞ Z))
         →  Tr∞ l m (fmap∞ Ass× (P |||+∞ fmap∞ (_,,_ x) (Z)))
 forcet (S|||+-∞ᵣ  P Z x l m x₂) = tnode (S|||+-pᵣ  P (forcep Z) x l m (forcet' l m (forcet x₂)))


 S|||-+∞ᵣ  : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                               (Z : Process∞ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ : Tr∞ l m (fmap+ (_,,_ x) Q |||+∞ Z))
         →  Tr∞ l m (fmap∞ Ass× (fmap∞ (_,,_ x) (Q |||+∞ Z )))
 forcet (S|||-+∞ᵣ  Q Z x l m tr) = tnode (S|||-+pᵣ Q (forcep Z) x l m (forcet' l m (forcet tr)))




 S|||-p+ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process  ∞ c₁)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ :  Tr+ l m (fmap (_,,_ x)  Q |||p+ Z))
         →  Tr+ l m (fmap+ Ass× (fmap+ (_,,_ x)(Q |||p+ Z)))
 S|||-p+ᵣ (terminate q) Z x l m tr = S|||--+ᵣ  Z q x l m tr
 S|||-p+ᵣ (node q) Z x l m tr      = S|||-++ᵣ q Z x l m tr


 S|||+-pᵣ  : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                               (Z : Process  ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ :  Tr+ l m (fmap+ (λ a → a ,, x) P |||+p Z))
         →  Tr+ l m (fmap+ Ass× (P |||+p fmap (_,,_ x) Z))
 S|||+-pᵣ  P (terminate x) x₁ l m x₂ = S|||+--ᵣ P m l x₁ x x₂
 S|||+-pᵣ  P (node x) x₁ l m x₂      = S|||+-+ᵣ P x x₁ l m x₂ 

 S|||+p-ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
                              (Q : Process  ∞ c₁)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂ :  Tr+ l m (fmap+ (λ a → a ,, x) (P |||+p Q)))
         →  Tr+ l m (fmap+ Ass× (P |||+p fmap (λ a → a ,, x) Q))
 S|||+p-ᵣ P (terminate x) m l x₁ x₂ = S|||+--ᵣ P m l x x₁ x₂
 S|||+p-ᵣ P (node x) m l x₁ x₂      = S|||++-ᵣ P x m l x₁ x₂ 


 S|||p+-ᵣ : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                              (Q : Process+ ∞ c₁)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₂)
         → (x₂ :  Tr+ l m (fmap+ (λ a → a ,, x) ( P |||p+ Q)))
         →  Tr+ l m (fmap+ Ass× (P |||p+ fmap+ (λ a → a ,, x) Q))
 S|||p+-ᵣ (terminate x) Q m l x₁ x₂ = S|||-+-ᵣ Q x x₁ l m x₂
 S|||p+-ᵣ (node x) Q m l x₁ x₂      = S|||++-ᵣ x Q m l x₁ x₂


 S|||p-+ᵣ : {c₀ c₁ c₂ : Choice}(P : Process  ∞ c₀)
                              (Z : Process+ ∞ c₂)
         → (x  : ChoiceSet c₁)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ :  Tr l m (node (fmap (λ a → a ,, x) ( P) |||p+ Z)))
         →  Tr+ l m (fmap+ Ass× (P |||p+ fmap+ (_,,_ x) Z))
 S|||p-+ᵣ (terminate x) Z x₁ l m x₂ = S|||--+ᵣ Z x₁ x l m (forcet' l m x₂)
 S|||p-+ᵣ (node x) Z x₁ l m x₂      = S|||+-+ᵣ x Z x₁ l m (forcet' l m x₂)


 S|||-+pᵣ : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
                              (Z : Process  ∞ c₂)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeChoice) 
         → (x₂ :  Tr+ l m (fmap+ (_,,_ x) Q |||+p Z))
         →  Tr+ l m (fmap+ Ass× (fmap+ (_,,_ x) (Q |||+p Z )))
 S|||-+pᵣ Q (terminate x) x₁ l m tr = S|||-+-ᵣ Q x₁ x l m tr
 S|||-+pᵣ Q (node x) x₁ l m tr      = S|||-++ᵣ Q x x₁ l m tr


 S|||+--ᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → (x₂ :  Tr+ l m (fmap+ (λ a → a ,, x₁) (fmap+ (λ a → a ,, x) P)))
         →  Tr+ l m (fmap+ Ass× (fmap+ (λ a → a ,, (x ,, x₁)) P))
 S|||+--ᵣ P .nothing .[] x x₁ empty                           = empty
 S|||+--ᵣ P m .(Lab P x₂ ∷ l) x x₁ (extc l .m x₂ x₃)          = extc l m x₂ (S|||∞--ᵣ (PE P x₂) m l x x₁ x₃)
 S|||+--ᵣ P m l x x₁ (intc .l .m x₂ x₃)                       = intc l m x₂ (S|||∞--ᵣ (PI P x₂) m l x x₁ x₃)
 S|||+--ᵣ P .(just ((PT P x₂ ,, x) ,, x₁)) .[] x x₁ (terc x₂) = terc x₂


 S|||∞--ᵣ : {c₀ c₁ c₂ : Choice}(P : Process∞ ∞ c₀)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₁)
         → (x₁ : ChoiceSet c₂)
         → (x₃ :  Tr∞ l m (fmap∞ (λ a → a ,, x₁) (fmap∞ (λ a → a ,, x) P )))
         →  Tr∞ l m (fmap∞ Ass× (fmap∞ (λ a → a ,, (x ,, x₁)) P))
 forcet (S|||∞--ᵣ P m l x x₁ x₃) = S|||p--ᵣ (forcep P) x x₁ l m (forcet x₃)


 S|||--+ᵣ  : {c₀ c₁ c₂ : Choice}(Z : Process+ ∞ c₂)
         → (q   : ChoiceSet c₁)
         → (x   : ChoiceSet c₀)
         → (l : List Label)
         → (m : Maybe maybeChoice)
         → (tr  :  Tr+ l m (fmap+ (_,,_ (x ,, q)) Z))
         →  Tr+ l m (fmap+ Ass× (fmap+ (_,,_ x) (fmap+ (_,,_ q) Z)))
 S|||--+ᵣ  Z q x .[] .nothing empty                          = empty
 S|||--+ᵣ  Z q x .(Lab Z x₁ ∷ l) m (extc l .m x₁ x₂)         = extc l m x₁ (S|||--∞ᵣ (PE Z x₁) q x l m x₂)
 S|||--+ᵣ  Z q x l m (intc .l .m x₁ x₂)                      = intc l m x₁ (S|||--∞ᵣ (PI Z x₁) q x l m x₂)
 S|||--+ᵣ  Z q x .[] .(just ((x ,, q) ,, PT Z x₁)) (terc x₁) = (terc x₁)


 S|||-+-ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process+ ∞ c₁)
         → (x₁ : ChoiceSet c₀)
         → (x  : ChoiceSet c₂)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (tr :  Tr+ l m (fmap+ (λ a → a ,, x) (fmap+ (_,,_ x₁) Q)))
         →  Tr+ l m (fmap+ Ass× (fmap+ (_,,_ x₁) (fmap+ (λ a → a ,, x) Q)))
 S|||-+-ᵣ Q x₁ x .[] .nothing empty                           = empty
 S|||-+-ᵣ Q x₁ x .(Lab Q x₂ ∷ l) m (extc l .m x₂ x₃)          = extc l m x₂ (S|||-∞-ᵣ (PE Q x₂) m l x₁ x x₃)
 S|||-+-ᵣ Q x₁ x l m (intc .l .m x₂ x₃)                       = intc l m x₂ (S|||-∞-ᵣ (PI Q x₂) m l x₁ x x₃)
 S|||-+-ᵣ Q x₁ x .[] .(just ((x₁ ,, PT Q x₂) ,, x)) (terc x₂) = (terc x₂)

 S|||--∞ᵣ : {c₀ c₁ c₂ : Choice}(Z : Process∞ ∞ c₂)
         → (q  : ChoiceSet c₁)
         → (x  : ChoiceSet c₀)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₂ :  Tr∞ l m (fmap∞ (_,,_ (x ,, q)) Z))
         →  Tr∞ l m (fmap∞ Ass× (fmap∞ (_,,_ x) (fmap∞ (_,,_ q) Z )))
 forcet (S|||--∞ᵣ Z q x l m x₂) = S|||--pᵣ (forcep Z) x q l m (forcet x₂)

 S|||-∞-ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process∞ ∞ c₁)
         → (m  : Maybe maybeChoice)
         → (l  : List Label)
         → (x  : ChoiceSet c₀)
         → (x₁ : ChoiceSet c₂)
         → (x₃ :  Tr∞ l m (fmap∞ (λ a → a ,, x₁) (fmap∞ (_,,_ x) Q)))
         →  Tr∞ l m (fmap∞ Ass× (fmap∞ (_,,_ x) (fmap∞ (λ a → a ,, x₁) Q)))
 forcet (S|||-∞-ᵣ Q m l x x₁ x₃) = S|||-p-ᵣ (forcep Q) x x₁ l m (forcet x₃)


 S|||--pᵣ : {c₀ c₁ c₂ : Choice}(Z : Process ∞ c₂)
         → (x : ChoiceSet c₀)
         → (q : ChoiceSet c₁)
         → (l : List Label)
         → (m : Maybe maybeChoice)
         → (x₂  :  Tr l m (fmap (_,,_ (x ,, q)) Z))
         →  Tr l m (fmap Ass× (fmap (_,,_ x)(fmap (_,,_ q) Z) ))
 S|||--pᵣ (terminate x) x₁ q l m x₂ = lemFmapR (λ x₃ → x) ((_,,_ (x₁ ,, q))) (terminate (x)) l m x₂
 S|||--pᵣ (node x)      x₁ q l m x₂ = tnode (S|||--+ᵣ x q x₁ l m (forcet' l m x₂))

 S|||-p-ᵣ : {c₀ c₁ c₂ : Choice}(Q : Process ∞ c₁)
         → (x₁ : ChoiceSet c₀)
         → (x  : ChoiceSet c₂)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₃ : Tr l m (fmap (λ a → a ,, x) (fmap (_,,_ x₁) (Q))))
         →  Tr l m (fmap Ass× (fmap (_,,_ x₁) (fmap (λ a → a ,, x) Q)))
 S|||-p-ᵣ (terminate x) x₁ x₂ l m x₃ = lemFmapR ((λ x₃ → x)) (λ x₄ → (x₁ ,, x) ,, x₂) (terminate (x)) l m x₃
 S|||-p-ᵣ (node x)      x₁ x₂ l m x₃ = tnode (S|||-+-ᵣ x x₁ x₂ l m (forcet' l m x₃)) 


 S|||p--ᵣ : {c₀ c₁ c₂ : Choice}(P : Process ∞ c₀)
         → (x₁ : ChoiceSet c₁)
         → (x  : ChoiceSet c₂)
         → (l  : List Label)
         → (m  : Maybe maybeChoice)
         → (x₃ :  Tr l m (fmap (λ a → a ,, x) (fmap (λ a → a ,, x₁) P)))
         →  Tr l m (fmap Ass× (fmap (λ a → a ,, (x₁ ,, x)) P))
 S|||p--ᵣ (terminate x) x₁ x₂ l m x₃ = lemFmapR (λ x₄ → x) (λ x₄ → (x ,, x₁) ,, x₂) (terminate (x)) l m x₃
 S|||p--ᵣ (node x)      x₁ x₂ l m x₃ = tnode (S|||+--ᵣ x m l x₁ x₂ (forcet' l m x₃))


≡|||+ : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀) (Q : Process+ ∞ c₁) (Z : Process+ ∞ c₂)
        → ((P |||++ Q) |||++ Z) ≡+  (fmap+ Ass× (P |||++ (Q  |||++ Z )))
≡|||+ P Q Z =  S|||+ P Q Z , S|||+ᵣ P Q Z
