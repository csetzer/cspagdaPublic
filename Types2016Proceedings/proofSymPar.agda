module proofSymPar where 


open import process 
open import Size
open import choiceSetU
open import Data.Maybe
open import Data.List
open import Data.Sum
open import renamingResult
open import TraceWithoutSize
open import RefWithoutSize
open import lemFmap
open import auxData
open import dataAuxFunction
open import Data.Product
open import label
open import restrict
open import parallelSimple
open import labelEq
open import Data.Bool.Base renaming (T to T')
open import traceEquivalence


trl : (Q : Label → Set) → (l l' : Label) → T'  (l ==l l' ) → Q l → Q l'
trl Q laba laba t q = q
trl Q laba labb () q
trl Q laba labc () q
trl Q labb laba () q
trl Q labb labb t q = q
trl Q labb labc () q
trl Q labc laba () q
trl Q labc labb () q
trl Q labc labc t q = q

sym : (l l' : Label) → T'  (l ==l l' ) → T'  (l' ==l l )
sym laba laba tt = tt
sym laba labb ()
sym laba labc ()
sym labb laba ()
sym labb labb tt = tt
sym labb labc ()
sym labc laba ()
sym labc labb ()
sym labc labc tt = tt

lemmaBool : (a b : Bool) → T' ( a ∧ b) →  T' a
lemmaBool false b ()
lemmaBool true false ()
lemmaBool true true tt = tt

lemmaBoolᵣ : (a b : Bool) → T' ( a ∧ b) →  T' b
lemmaBoolᵣ false false ()
lemmaBoolᵣ true false ()
lemmaBoolᵣ false true ()
lemmaBoolᵣ true true tt = tt


lemmaBool'aux : (a b c : Bool) → T' ( a ∧ b ∧ c) →  T' c
lemmaBool'aux a b c p = let
                            q : T' ( b ∧ c)
                            q = lemmaBoolᵣ a  ( b ∧ c) p
                        in lemmaBoolᵣ b c q

lemmaBool' : (a b c : Bool) → T' ( a ∧ b ∧ c) →  T' c
lemmaBool' false false false ()
lemmaBool' false false true ()
lemmaBool' false true false ()
lemmaBool' false true true ()
lemmaBool' true false false ()
lemmaBool' true false true ()
lemmaBool' true true false ()
lemmaBool' true true true tt = tt 

lemmaBool'' : (a b c : Bool) →  T' a → T' b → T' c → T' ( a ∧ b ∧ c)
lemmaBool'' false b c () x₁ x₂
lemmaBool'' true false c x () x₂
lemmaBool'' true true c x tt x₂ = x₂



mutual 
 S[]+ : {c₀ c₁ : Choice} (P : Process+ ∞ c₀) (A  B : Label → Bool) (Q : Process+ ∞ c₁)
        → (P [ A ]||+[ B ] Q) ⊑+ fmap+ swap× ((Q [ B ]||+[ A ] P))

 S[]+ P A B Q .[] .nothing empty = empty
 S[]+ P A B Q .(Lab Q a ∷ l) m (extc l .m (inj₁ (inj₁ (sub a x))) x₁) =  extc l m (inj₁ (inj₂ ( sub a x))) (S[]+∞ P A B (PE Q a) l m x₁)
 S[]+ P A B Q .(Lab P a ∷ l) m (extc l .m (inj₁ (inj₂ (sub a x))) x₁) =  extc l m (inj₁ (inj₁ (sub a x))) (S[]∞+ (PE P a) A B Q l m x₁)
 S[]+ P A B Q .(Lab Q x ∷ l) m (extc l .m (inj₂ (sub (x ,, x₁) x₂)) x₃) = let
                                                                            lxlx₁ : T' (Lab Q x ==l Lab P x₁)
                                                                            lxlx₁   =  lemmaBool (Lab Q x ==l Lab P x₁)
                                                                                                 (B (Lab Q x) ∧ A (Lab P x₁)) x₂

                                                                            BQx : T' (B (Lab Q x))
                                                                            BQx = lemmaBool (B (Lab Q x)) (A (Lab P x₁))
                                                                                   (lemmaBoolᵣ ((Lab Q x ==l Lab P x₁))
                                                                                               (B (Lab Q x) ∧ A (Lab P x₁)) x₂)
                                                                          
                                                                            APx₁ : T' (A (Lab P x₁))
                                                                            APx₁ = lemmaBool' ((Lab Q x ==l Lab P x₁))
                                                                                                    (B (Lab Q x)) (A (Lab P x₁)) x₂ 
                                                

                                                                            lx₁lx : T' (Lab P x₁ ==l Lab Q x)
                                                                            lx₁lx = sym ((Lab Q x)) ((Lab P x₁)) lxlx₁
                                                                            
                                                                            x₂'  : T' ((Lab P x₁ ==l Lab Q x) ∧ A (Lab P x₁) ∧ B (Lab Q x))
                                                                            x₂'  =  lemmaBool'' (((Lab P x₁ ==l Lab Q x)))((A(Lab P x₁)))
                                                                                                           (B (Lab Q x)) lx₁lx APx₁ BQx

                                                                            auxproof : Tr+ (Lab P x₁ ∷ l) m (P [ A ]||+[ B ] Q) 
                                                                            auxproof = extc l m (inj₂ (sub (x₁ ,, x) x₂'))
                                                                                                 (S[]∞∞ (PE P x₁) A B (PE Q x) l m x₃)


                                                                            auxproof' : Tr+ (Lab Q x ∷ l) m (P [ A ]||+[ B ] Q) 
                                                                            auxproof' = trl (λ l' → Tr+ (l' ∷ l) m (P [ A ]||+[ B ] Q))
                                                                                            (Lab P x₁)
                                                                                            (Lab Q x)
                                                                                            lx₁lx
                                                                                            auxproof
                                                                          in auxproof'
                                                                          
 S[]+ P A B Q l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₂ x) (S[]+∞ P A B (PI Q x) l m x₁)
 S[]+ P A B Q l m (intc .l .m (inj₂ y) x₁) = intc l m (inj₁ y) (S[]∞+ (PI P y) A B Q l m x₁)
 S[]+ P A B Q .[] .(just (PT P x₁ ,, PT Q x)) (terc (x ,, x₁)) = terc (x₁ ,, x)

 S[]+∞  :  {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (A  B : Label → Bool)
         → (Q : Process∞  ∞ c₁)
         → Ref∞  (P [ A ]||+∞[ B ] Q) (fmap∞ swap× ((Q [ B ]||∞+[ A ] P))) 
 forcet (S[]+∞ P A B Q l m x) = tnode (S[]+p P A B (forcep Q) l m (forcet' l m (forcet x)))


 S[]∞+  :  {c₀ c₁ : Choice}
         → (P : Process∞  ∞ c₀)
         → (A  B : Label → Bool)
         → (Q : Process+ ∞ c₁)
         → Ref∞ (P [ A ]||∞+[ B ] Q) (fmap∞ swap× ((Q [ B ]||+∞[ A ] P)))
 forcet (S[]∞+ P  A B Q l m x) = tnode (S[]p+ (forcep P) A B Q l m ((forcet' l m (forcet x))))

 S[]∞∞  :  {c₀ c₁ : Choice}
         → (P : Process∞ ∞ c₀)
         → (A  B : Label → Bool)
         → (Q : Process∞  ∞ c₁)
         → Ref∞  (P [ A ]||∞[ B ] Q) (fmap∞ swap× ((Q [ B ]||∞[ A ] P))) 
 forcet (S[]∞∞ P A B Q l m x) = S[]pp ((forcep P)) A B (forcep Q) l m (forcet x) 


 S[]pp  :  {c₀ c₁ : Choice}
         → (P : Process ∞ c₀)
         → (A  B : Label → Bool)
         → (Q : Process  ∞ c₁)
         → Ref  (P [ A ]||[ B ] Q) (fmap swap× ((Q [ B ]||[ A ] P))) 
 S[]pp (terminate p) A B (terminate q) .[] .(just (p ,, q)) (ter .(p ,, q)) = ter (p ,, q)
 S[]pp (terminate p) A B (terminate q) .[] .nothing (empty .(p ,, q)) = empty (p ,, q)
 S[]pp (terminate p) A B (node q) .[] .nothing (tnode empty) = tnode empty
 S[]pp (terminate p) A B (node q) .(Lab q a ∷ l) m (tnode (extc l .m (sub a x) x₁)) = tnode (extc l m (sub a x)
                                                                                        (lemFmap∞ (λ a₁ → a₁ ,, p)
                                                                                              swap× (PE (q ↾+ (B ∖ A)) (sub a x)) l m x₁))
 S[]pp (terminate p) A B (node q) l m (tnode (intc .l .m x x₁)) = tnode (intc l m x (lemFmap∞ (λ a → a ,, p)
                                                                                                swap× (PI (q ↾+ (B ∖ A)) x) l m x₁))
 S[]pp (terminate p) A B (node q) .[] .(just (p ,, PT q x)) (tnode (terc x)) = tnode (terc x)
 S[]pp (node p) A B (terminate q) .[] .nothing (tnode empty) = tnode empty
 S[]pp (node p) A B (terminate q) .(Lab p a ∷ l) m (tnode (extc l .m (sub a x) x₁)) = tnode (extc l m (sub a x)
                                                                                                (lemFmap∞ (_,,_ q) swap×
                                                                                                     (PE (p ↾+ (A ∖ B)) (sub a x)) l m x₁))
 S[]pp (node p) A B (terminate q) l m (tnode (intc .l .m x x₁)) = tnode (intc l m x (lemFmap∞ (_,,_ q) swap× (PI (p ↾+ (A ∖ B)) x) l m x₁))
 S[]pp (node p) A B (terminate q) .[] .(just (PT p x ,, q)) (tnode (terc x)) = tnode (terc x)
 S[]pp (node p) A B (node q) .[] .nothing (tnode empty) = tnode empty
 S[]pp (node p) A B (node q) .(Lab q a ∷ l) m (tnode (extc l .m (inj₁ (inj₁ (sub a x))) x₁)) = tnode (extc l m (inj₁ (inj₂ (sub a x)))
                                                                                                           (S[]+∞ p A B (PE q a) l m x₁))
 S[]pp (node p) A B (node q) .(Lab p a ∷ l) m (tnode (extc l .m (inj₁ (inj₂ (sub a x))) x₁)) = tnode (extc l m (inj₁ (inj₁ (sub a x)))
                                                                                                           (S[]∞+ (PE p a) A B q l m x₁))
 S[]pp (node p) A B (node q) .(Lab q x ∷ l) m (tnode (extc l .m (inj₂ (sub (x ,, x₁) x₂)) x₃)) = let
                                                                                                  lxlx :  T' (Lab q x ==l Lab p x₁)
                                                                                                  lxlx = lemmaBool (Lab q x ==l Lab p x₁)
                                                                                                                   (B (Lab q x)
                                                                                                                      ∧ A (Lab p x₁)) x₂
                                                                                                  
                                                                                                  BQx : T' (B (Lab q x))
                                                                                                  BQx = lemmaBool (B (Lab q x))
                                                                                                                  (A (Lab p x₁))
                                                                                                                  (lemmaBoolᵣ
                                                                                                                  ((Lab q x ==l Lab p x₁))
                                                                                                                   (B (Lab q x) ∧
                                                                                                                          A (Lab p x₁)) x₂)
                                                                          

                                                                                                  APx₁ : T' (A (Lab p x₁))
                                                                                                  APx₁ = lemmaBool' ((Lab q x ==l Lab p x₁))
                                                                                                                     (B (Lab q x))
                                                                                                                     (A (Lab p x₁)) x₂

                                                                                                  lx₁lx : T' (Lab p x₁ ==l Lab q x)
                                                                                                  lx₁lx = sym (Lab q x) (Lab p x₁) lxlx

                                                                                                  x₂'  : T' ((Lab p x₁ ==l Lab q x)
                                                                                                              ∧ A (Lab p x₁)
                                                                                                              ∧ B (Lab q x))
                                                                                                  x₂'  =  lemmaBool''
                                                                                                           ((Lab p x₁ ==l Lab q x))
                                                                                                              (A (Lab p x₁))
                                                                                                               (B (Lab q x))
                                                                                                                 lx₁lx APx₁ BQx

                                                                                                  auxproof : Tr+ (Lab p x₁ ∷ l)
                                                                                                                   m (p [ A ]||+[ B ] q) 
                                                                                                  auxproof = extc l m (inj₂ (sub (x₁ ,, x)
                                                                                                                      x₂'))
                                                                                                                      (S[]∞∞ (PE p x₁)
                                                                                                                      A B (PE q x) l m x₃)


                                                                                                  auxproof' : Tr+ (Lab q x ∷ l) m
                                                                                                                     (p [ A ]||+[ B ] q) 
                                                                                                  auxproof' = trl (λ l' → Tr+ (l' ∷ l)
                                                                                                                    m (p [ A ]||+[ B ] q))
                                                                                                                      (Lab p x₁)
                                                                                                                      (Lab q x)lx₁lx
                                                                                                                      auxproof
                                                                                                in (tnode auxproof')
                                                                                                
 S[]pp (node p) A B (node q) l m (tnode (intc .l .m (inj₁ x) x₁)) = tnode (intc l m (inj₂ x) (S[]+∞ p A B (PI q x) l m x₁))
 S[]pp (node p) A B (node q) l m (tnode (intc .l .m (inj₂ y) x₁)) = tnode ( (intc l m (inj₁ y) (S[]∞+ (PI p y) A B q l m x₁)))
 S[]pp (node p) A B (node q) .[] .(just (PT p x₁ ,, PT q x)) (tnode (terc (x ,, x₁))) = tnode (terc (x₁ ,, x))


 S[]+p  : {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (A  B : Label → Bool)
         → (Q : Process  ∞ c₁)
         → Ref+ (P [ A ]||+p[ B ] Q) (fmap+ swap× ((Q [ B ]||p+[ A ] P)))
 S[]+p P A B (terminate x) l m q = lemFmap+ (_,,_ x) swap× (P ↾+ (A ∖ B)) l m q
 S[]+p P A B (node Q) l m q = S[]+ P A B Q l m q


 S[]p+  : {c₀ c₁ : Choice}
         → (P : Process ∞ c₀)
         → (A  B : Label → Bool)         
         → (Q : Process+ ∞ c₁)
         → Ref+ (P [ A ]||p+[ B ] Q) (fmap+ swap× ((Q [ B ]||+p[ A ] P)))
 S[]p+ (terminate x) Q l m q = lemFmap+ (λ a → a ,, x) swap× (m ↾+ (l ∖ Q)) q
 S[]p+ (node P) Q l m q = S[]+ P Q l m q



mutual 
 S[]+ᵣ : {c₀ c₁ : Choice} (P : Process+ ∞ c₀) (A  B : Label → Bool) (Q : Process+ ∞ c₁)
        →  fmap+ swap× ((Q [ B ]||+[ A ] P))  ⊑+ (P [ A ]||+[ B ] Q)

 S[]+ᵣ P A B Q .[] .nothing empty = empty
 S[]+ᵣ P A B Q .(Lab P a ∷ l) m (extc l .m (inj₁ (inj₁ (sub a x))) x₁) = extc l m (inj₁ (inj₂ (sub a x))) (S[]∞+ᵣ (PE P a) A B Q l m x₁)
 S[]+ᵣ P A B Q .(Lab Q a ∷ l) m (extc l .m (inj₁ (inj₂ (sub a x))) x₁) = extc l m (inj₁ (inj₁ (sub a x))) (S[]+∞ᵣ P A B (PE Q a) l m x₁)
 S[]+ᵣ P A B Q .(Lab P x ∷ l) m (extc l .m (inj₂ (sub (x ,, x₁) x₂)) x₃) =  let
                                                                                                  lx₁lx : T' (Lab P x ==l Lab Q x₁)
                                                                                                  lx₁lx = lemmaBool (Lab P x ==l Lab Q x₁)
                                                                                                                    (A (Lab P x) ∧
                                                                                                                     B (Lab Q x₁)) x₂

                                                                                                  lxlx :  T' (Lab Q x₁ ==l Lab P x)
                                                                                                  lxlx = sym (Lab P x)
                                                                                                             (Lab Q x₁)
                                                                                                             lx₁lx
                                                                                                  
                                                                                                  BQx : T' (B (Lab Q x₁))
                                                                                                  BQx = lemmaBool' (Lab P x ==l Lab Q x₁)
                                                                                                                   (A (Lab P x))
                                                                                                                   (B (Lab Q x₁)) x₂ 

                                                                                                  APx₁ : T' (A (Lab P x))
                                                                                                  APx₁ = lemmaBool (A (Lab P x))
                                                                                                                   (B (Lab Q x₁))
                                                                                                                   (lemmaBoolᵣ
                                                                                                                   (Lab P x ==l Lab Q x₁)
                                                                                                                   ( A (Lab P x) ∧
                                                                                                                      B (Lab Q x₁) ) x₂)
                                                                                                                                                                                                                                                                             
                                                                                                  x₂'  : T' ((Lab Q x₁ ==l Lab P x)
                                                                                                         ∧ (B (Lab Q x₁))
                                                                                                         ∧ (A (Lab P x)))
                                                                                                  x₂'  = lemmaBool''
                                                                                                         (Lab Q x₁ ==l Lab P x)
                                                                                                         (B (Lab Q x₁))
                                                                                                         (A (Lab P x))
                                                                                                         lxlx BQx APx₁

                                                                                                  auxproof : Tr+ (Lab Q x₁ ∷ l) m
                                                                                                                 (fmap+ swap×
                                                                                                                    (Q [ B ]||+[ A ] P))

                                                                                                  auxproof = extc l m
                                                                                                               (inj₂ (sub ( x₁ ,, x) x₂'))
                                                                                                                   (S[]∞∞ᵣ (PE P x) A B
                                                                                                                         (PE Q x₁) l m x₃)


                                                                                                  auxproof' : Tr+ (Lab (P [ A ]||+[ B ] Q)
                                                                                                              (inj₂ (sub (x ,, x₁) x₂)) ∷ l)
                                                                                                                  m (fmap+ swap×
                                                                                                                      (Q [ B ]||+[ A ] P))
                                                                                                  auxproof' = trl ((λ l' → Tr+ (l' ∷ l)
                                                                                                                    m  ((fmap+ swap×
                                                                                                                     (Q [ B ]||+[ A ] P)))))
                                                                                                                        (Lab Q x₁)
                                                                                                                        (Lab P x)
                                                                                                                        lxlx auxproof 
                                                                                                in auxproof'   
 S[]+ᵣ P A B Q l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₂ x) (S[]∞+ᵣ (PI P x) A B Q l m x₁)
 S[]+ᵣ P A B Q l m (intc .l .m (inj₂ y) x₁) = intc l m (inj₁ y) (S[]+∞ᵣ P A B (PI Q y) l m x₁)
 S[]+ᵣ P A B Q .[] .(just (PT P x ,, PT Q x₁)) (terc (x ,, x₁)) = terc ( (x₁ ,, x))


 S[]+∞ᵣ  :  {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (A  B : Label → Bool)
         → (Q : Process∞  ∞ c₁)
         → Ref∞  (fmap∞ swap× ((Q [ B ]||∞+[ A ] P)))   (P [ A ]||+∞[ B ] Q)
 forcet (S[]+∞ᵣ P A B Q l m x) = tnode (S[]+pᵣ P A B (forcep Q) l m (forcet' l m (forcet x)))


 S[]∞+ᵣ  :  {c₀ c₁ : Choice}
         → (P : Process∞  ∞ c₀)
         → (A  B : Label → Bool)
         → (Q : Process+ ∞ c₁)
         → Ref∞  (fmap∞ swap× ((Q [ B ]||+∞[ A ] P))) (P [ A ]||∞+[ B ] Q)
 forcet (S[]∞+ᵣ P  A B Q l m x) = tnode (S[]p+ᵣ (forcep P) A B Q l m ((forcet' l m (forcet x))))



 S[]+pᵣ  : {c₀ c₁ : Choice}
         → (P : Process+ ∞ c₀)
         → (A  B : Label → Bool)
         → (Q : Process  ∞ c₁)
         → Ref+  (fmap+ swap× ((Q [ B ]||p+[ A ] P))) (P [ A ]||+p[ B ] Q)
 S[]+pᵣ P A B (terminate x) l m q = lemFmap+R (_,,_ x) swap× (P ↾+ (A ∖ B)) l m q
 S[]+pᵣ P A B (node Q) l m q = S[]+ᵣ P A B Q l m q


 S[]p+ᵣ  : {c₀ c₁ : Choice}
         → (P : Process ∞ c₀)
         → (A  B : Label → Bool)         
         → (Q : Process+ ∞ c₁)
         → Ref+  (fmap+ swap× ((Q [ B ]||+p[ A ] P))) (P [ A ]||p+[ B ] Q)
 S[]p+ᵣ (terminate x) Q l m q = lemFmap+R (λ a → a ,, x) swap× (m ↾+ (l ∖ Q)) q
 S[]p+ᵣ (node P) Q l m q = S[]+ᵣ P Q l m q



 S[]∞∞ᵣ  :  {c₀ c₁ : Choice}
         → (P : Process∞ ∞ c₀)
         → (A  B : Label → Bool)
         → (Q : Process∞  ∞ c₁)
         → Ref∞  (fmap∞ swap× ((Q [ B ]||∞[ A ] P)))   (P [ A ]||∞[ B ] Q)
 forcet (S[]∞∞ᵣ P A B Q l m x) = S[]ppᵣ ((forcep P)) A B (forcep Q) l m (forcet x) 

 S[]ppᵣ  :  {c₀ c₁ : Choice}
         → (P : Process ∞ c₀)
         → (A  B : Label → Bool)
         → (Q : Process  ∞ c₁)
         → Ref  (fmap swap× ((Q [ B ]||[ A ] P))) (P [ A ]||[ B ] Q)
 S[]ppᵣ (terminate x) A B (terminate x₁) .[] .(just (x ,, x₁)) (ter .(x ,, x₁)) = ter (x ,, x₁)
 S[]ppᵣ (terminate x) A B (terminate x₁) .[] .nothing (empty .(x ,, x₁)) = empty (x ,, x₁)
 S[]ppᵣ (terminate x) A B (node x₁) .[] .nothing (tnode empty) = tnode empty
 S[]ppᵣ (terminate x) A B (node x₁) .(Lab x₁ a ∷ l) m (tnode (extc l .m (sub a x₂) x₃)) = tnode (extc l m (sub a x₂)
                                                                                                (lemFmap∞R (λ a₁ → a₁ ,, x)
                                                                                                     swap× (PE (x₁ ↾+ (B ∖ A))
                                                                                                                (sub a x₂)) l m x₃))
 S[]ppᵣ (terminate x) A B (node x₁) l m (tnode (intc .l .m x₂ x₃)) = tnode (intc l m x₂
                                                                             (lemFmap∞R (λ a → a ,, x)
                                                                                  swap× (PI (x₁ ↾+ (B ∖ A)) x₂)
                                                                                                         l m x₃))
 S[]ppᵣ (terminate x) A B (node x₁) .[] .(just (x ,, PT x₁ x₂)) (tnode (terc x₂)) = tnode (terc x₂)
 S[]ppᵣ (node x) A B (terminate x₁) .[] .nothing (tnode empty) = tnode empty
 S[]ppᵣ (node x) A B (terminate x₁) .(Lab x a ∷ l) m (tnode (extc l .m (sub a x₂) x₃)) = tnode (extc l m (sub a x₂)
                                                                              (lemFmap∞R (_,,_ x₁)
                                                                                   swap× (PE (x ↾+ (A ∖ B))
                                                                                           (sub a x₂)) l m x₃))
 S[]ppᵣ (node x) A B (terminate x₁) l m (tnode (intc .l .m x₂ x₃)) = tnode (intc l m x₂
                                                                              (lemFmap∞R (_,,_ x₁)
                                                                                  swap× (PI (x ↾+ (A ∖ B)) x₂)
                                                                                                        l m x₃))
 S[]ppᵣ (node x) A B (terminate x₁) .[] .(just (PT x x₂ ,, x₁)) (tnode (terc x₂)) = tnode (terc x₂)
 S[]ppᵣ (node x) A B (node x₁) .[] .nothing (tnode empty) = tnode empty
 S[]ppᵣ (node x) A B (node x₁) .(Lab x a ∷ l) m (tnode (extc l .m (inj₁ (inj₁ (sub a x₂))) x₃)) = tnode (extc l m
                                                                                                         (inj₁ (inj₂ (sub a x₂)))
                                                                                                            (S[]∞+ᵣ (PE x a) A B x₁ l m x₃))
 S[]ppᵣ (node x) A B (node x₁) .(Lab x₁ a ∷ l) m (tnode (extc l .m (inj₁ (inj₂ (sub a x₂))) x₃)) = tnode (extc l m
                                                                                                          (inj₁ (inj₁ (sub a x₂)))
                                                                                                            (S[]+∞ᵣ x A B (PE x₁ a) l m x₃))
 S[]ppᵣ (node P) A B (node Q) .(Lab P x ∷ l) m (tnode (extc l .m (inj₂ (sub (x ,, x₁) x₂)) x₃)) =  let
                                                                                                  lx₁lx : T' (Lab P x ==l Lab Q x₁)
                                                                                                  lx₁lx = lemmaBool (Lab P x ==l Lab Q x₁)
                                                                                                                    (A (Lab P x) ∧
                                                                                                                     B (Lab Q x₁)) x₂

                                                                                                  lxlx :  T' (Lab Q x₁ ==l Lab P x)
                                                                                                  lxlx = sym (Lab P x)
                                                                                                             (Lab Q x₁)
                                                                                                             lx₁lx
                                                                                                  
                                                                                                  BQx : T' (B (Lab Q x₁))
                                                                                                  BQx = lemmaBool' (Lab P x ==l Lab Q x₁)
                                                                                                                   (A (Lab P x))
                                                                                                                   (B (Lab Q x₁)) x₂ 

                                                                                                  APx₁ : T' (A (Lab P x))
                                                                                                  APx₁ = lemmaBool (A (Lab P x))
                                                                                                                   (B (Lab Q x₁))
                                                                                                                   (lemmaBoolᵣ
                                                                                                                   (Lab P x ==l Lab Q x₁)
                                                                                                                   ( A (Lab P x) ∧
                                                                                                                      B (Lab Q x₁) ) x₂)
                                                                                                                                                                                                                                                                             
                                                                                                  x₂'  : T' ((Lab Q x₁ ==l Lab P x)
                                                                                                         ∧ (B (Lab Q x₁))
                                                                                                         ∧ (A (Lab P x)))
                                                                                                  x₂'  = lemmaBool''
                                                                                                         (Lab Q x₁ ==l Lab P x)
                                                                                                         (B (Lab Q x₁))
                                                                                                         (A (Lab P x))
                                                                                                         lxlx BQx APx₁

                                                                                                  auxproof : Tr+ (Lab Q x₁ ∷ l) m
                                                                                                                 (fmap+ swap×
                                                                                                                    (Q [ B ]||+[ A ] P))

                                                                                                  auxproof = extc l m
                                                                                                               (inj₂ (sub ( x₁ ,, x) x₂'))
                                                                                                                   (S[]∞∞ᵣ (PE P x) A B
                                                                                                                         (PE Q x₁) l m x₃)


                                                                                                  auxproof' : Tr+ (Lab (P [ A ]||+[ B ] Q)
                                                                                                              (inj₂ (sub (x ,, x₁) x₂)) ∷ l)
                                                                                                                  m (fmap+ swap×
                                                                                                                      (Q [ B ]||+[ A ] P))
                                                                                                  auxproof' = trl ((λ l' → Tr+ (l' ∷ l)
                                                                                                                    m  ((fmap+ swap×
                                                                                                                     (Q [ B ]||+[ A ] P)))))
                                                                                                                        (Lab Q x₁)
                                                                                                                        (Lab P x)
                                                                                                                        lxlx auxproof 
                                                                                                in  tnode auxproof' 
 S[]ppᵣ (node x) A B (node x₁) l m (tnode (intc .l .m (inj₁ x₂) x₃)) =  tnode (intc l m (inj₂ x₂) (S[]∞+ᵣ (PI x x₂) A B x₁ l m x₃))
 S[]ppᵣ (node x) A B (node x₁) l m (tnode (intc .l .m (inj₂ y) x₃)) =  tnode (intc l m (inj₁ y) (S[]+∞ᵣ x A B (PI x₁ y) l m x₃)) 
 S[]ppᵣ (node x) A B (node x₁) .[] .(just (PT x x₂ ,, PT x₁ x₃)) (tnode (terc (x₂ ,, x₃))) = tnode (terc (x₃ ,, x₂))


 ≡□+ : {c₀ c₁ : Choice} (P : Process+ ∞ c₀)(A  B : Label → Bool)(Q : Process+ ∞ c₁)
        → (P [ A ]||+[ B ] Q) ≡+  (fmap+ swap× ((Q [ B ]||+[ A ] P)))
 ≡□+  P A B Q = (S[]+ P A B Q) , (S[]+ᵣ P A B Q)

