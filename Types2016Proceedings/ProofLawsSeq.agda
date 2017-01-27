module ProofLawsSeq where 

open import process 
open import Size
open import Level
open import choiceSetU
open import auxData
open import Data.Maybe
open import Data.Product
open import Data.Fin
open import Data.List
open import Data.Sum
open import label
open import dataAuxFunction
open import externalChoice
open import sequentialCompositionRev
open import renamingResult
open import TraceWithoutSize
open import RefWithoutSize
open import primitiveProcess
open import traceEquivalence
open import Data.Product



lemTrTerminateBind : (c : Choice)(P : Process+ ∞ c)(x : ChoiceSet (T P))
                     → Tr∞ [] (just (PT P x)) (PI (P ⟫=+ terminate) (inj₂ x))
forcet (lemTrTerminateBind  c P x) = ter (PT P x)


lemTrTerminateBind' : (c₀ c₁ c₂ : Choice)
                      (P : Process+ ∞ c₀)
                      (Q : ChoiceSet c₀ → Process ∞ c₁)
                      (R : ChoiceSet c₁ → Process ∞ c₂)
                      (x  : Fin 0)
                     → Tr∞ [] (just (PT (_⟫=+_ P (λ x₁ → _⟫=_ (Q x₁) R)) x))(PI (_⟫=+_ (_⟫=+_ P Q) R) (inj₂ x))
forcet (lemTrTerminateBind'  c P Q R x q ())



--------------------------------------------------------------------------------------------------------------------


stopSeq : {c₀ : Choice} (a : ChoiceSet c₀)(P : ChoiceSet c₀ → Process ∞ c₀)
               → (STOP c₀ ⟫= P)  ⊑ STOP c₀ 
stopSeq a P .[] .nothing (tnode empty) = tnode empty
stopSeq a P .(efq _ ∷ l) m (tnode (extc l .m () x₁))
stopSeq a P l m (tnode (intc .l .m () x₁))
stopSeq a P .[] .(just (efq _)) (tnode (terc ()))


stopSeqᵣ : {c₀ : Choice} (a : ChoiceSet c₀)(P : ChoiceSet c₀ → Process ∞ c₀)
               →  STOP c₀  ⊑ (STOP c₀ ⟫= P)
stopSeqᵣ a P .[] .nothing (tnode empty) = tnode empty
stopSeqᵣ a P .(efq _ ∷ l) m (tnode (extc l .m () x₁))
stopSeqᵣ a P l m (tnode (intc .l .m (inj₁ ()) x₁))
stopSeqᵣ a P l m (tnode (intc .l .m (inj₂ ()) x₁))
stopSeqᵣ a P .[] .(just (PT (process+ (fin 0) efq efq (fin 0) efq (fin 0) efq "STOP" ⟫=+ P) _)) (tnode (terc ())) 

≡stopSeq : {c₀ : Choice} (a : ChoiceSet c₀)(P : ChoiceSet c₀ → Process ∞ c₀)
        → STOP c₀ ≡  (STOP c₀ ⟫= P)
≡stopSeq a P = (stopSeqᵣ a P) , (stopSeq a P)




---------------------------------------------------------------------------------------------------------------------




unitSeqL : {c₀ c₁  : Choice} (a : ChoiceSet c₀)(P : ChoiceSet c₀ → Process ∞ c₁)
               → (terminate a ⟫= P)  ⊑  P a
unitSeqL  a P l m q = q




unitSeqLᵣ : {c₀ c₁  : Choice} (a : ChoiceSet c₀)(P : ChoiceSet c₀ → Process ∞ c₁)
               → P a ⊑ (terminate a ⟫= P)
unitSeqLᵣ {c₀} {c₁} a P l m q = q


≡unitSeq : {c₀ : Choice} (a : ChoiceSet c₀)(P : ChoiceSet c₀ → Process ∞ c₀)
        → P a ≡ (terminate a ⟫= P)
≡unitSeq a P = (unitSeqL a P) , unitSeqLᵣ a P




-------------------------------------------------------------------------------------------------------------------------------

lemTrTerminateBind'' : (c : Choice)(P : Process+ ∞ c) (x : Fin 0)
                     → Tr+ [] (just (PT (P ⟫=+ terminate) x)) P
lemTrTerminateBind'' c P ()



lemtr+trterminate : (c₀ : Choice) → (m : Maybe (ChoiceSet c₀)) → (P : Process+ ∞ c₀) → (l : List Label) →
                    (y : ChoiceSet (T P)) → (traux : Tr {c₀} l m (terminate (PT P y))) → Tr+ {c₀} l m P
lemtr+trterminate c₀ .(just (PT P y)) P .[] y (ter .(PT P y)) = terc y
lemtr+trterminate c₀ .nothing P .[] y (empty .(PT P y)) = empty



mutual
  unitSeqR : {c₀ : Choice} (P : Process ∞ c₀)
             → (P  ⟫=  terminate)  ⊑  P
  unitSeqR (terminate x) l m q = q
  unitSeqR (node x) l m q      = tnode (unitSeqR₊ x l m (forcet' l m q))


  unitSeqR₊ : {c₀ : Choice} (P : Process+ ∞ c₀)
               → (P  ⟫=+  terminate) ⊑+ P
  unitSeqR₊ P .[] .nothing empty                 = empty
  unitSeqR₊ P .(Lab P x ∷ l) m (extc l .m x x₁)  = extc l m x (unitSeqR∞ (PE P x) l m x₁)
  unitSeqR₊ P l m (intc .l .m x x₁)              = intc l m (inj₁ x) (unitSeqR∞ (PI P x) l m x₁)
  unitSeqR₊ {c₀} P .[] .(just (PT P x)) (terc x) = intc [] (just (PT P x)) (inj₂ x) (lemTrTerminateBind  c₀ P x)


  unitSeqR∞ : {c₀  : Choice} (P : Process∞ ∞ c₀)
                 → (P  ⟫=∞  terminate)  ⊑∞  P
  forcet (unitSeqR∞ P l m q) = unitSeqR (forcep P) l m (forcet q)

mutual
  unitSeq₂ᵣ : {c₀  : Choice} (P : Process ∞ c₀)
                 → P ⊑  (P  ⟫=  terminate)
  unitSeq₂ᵣ {c₀} (terminate x) l m x₁ = x₁
  unitSeq₂ᵣ {c₀} (node x) l m x₁ = tnode (unitSeq₂ᵣ₊ x l m (forcet' l m x₁))

  unitSeq₂ᵣ₊ : {c₀  : Choice} (P : Process+ ∞ c₀)
                 → P ⊑+  (P  ⟫=+  terminate)
  unitSeq₂ᵣ₊ P .[] .nothing (empty {P = .(P ⟫=+ terminate)}) = empty
  unitSeq₂ᵣ₊ P .(Lab P x ∷ l) m (extc {P = .(P ⟫=+ terminate)} l .m x x₁) = extc l m x (unitSeq₂ᵣ∞ (PE P x) l m x₁)
  unitSeq₂ᵣ₊ {c₀} P l m (intc {P = .(_⟫=+_ {∞} {c₀} {c₀} P terminate)} .l .m (inj₁ x) x₁) = intc l m x (unitSeq₂ᵣ∞ (PI P x) l m x₁)
  unitSeq₂ᵣ₊ {c₀} P l m (intc {P = .(_⟫=+_ {∞} {c₀} {c₀} P terminate)} .l .m (inj₂ y) x₁) =
       let
          s : Set
          s = Tr {c₀} l m  (forcep (PI (_⟫=+_ {∞} {c₀} {c₀} P terminate) (inj₂ y)) {∞})


          traux : Tr {c₀} l m (terminate (PT P y))
          traux = forcet x₁
          
       in lemtr+trterminate c₀ m P l y traux 
  unitSeq₂ᵣ₊ {c₀} P .[] .(just (PT (P ⟫=+ terminate) x)) (terc {P = .(P ⟫=+ terminate)} x) = lemTrTerminateBind'' c₀ P x

  unitSeq₂ᵣ∞ : {c₀  : Choice} (P : Process∞ ∞ c₀)
                 → P ⊑∞  (P  ⟫=∞  terminate)
  forcet (unitSeq₂ᵣ∞ {c₀} P l m x) = unitSeq₂ᵣ (forcep P {∞}) l m (forcet x)




≡unitSeq₂ : {c₀ c₁ : Choice} (P : Process ∞ c₀)
        →  P  ≡  (P  ⟫= terminate)
≡unitSeq₂ {c₀} {c₁} P = (unitSeq₂ᵣ P) , (unitSeqR P)


----------------------------------------------------------------------------------------------------------


mutual
  assSeq : {c₀ c₁ c₂ : Choice} (P : Process ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → ((P  ⟫=  Q) ⟫= R)  ⊑  (P  ⟫=  ( λ x → Q x ⟫= R  ))
  assSeq {c₀} {c₁} {c₂} (terminate x) Q R l m q = q
  assSeq {c₀} {c₁} {c₂} (node x) Q R l m q = tnode (assSeq₁₋₃₊ x Q R l m (forcet' l m q))


  assSeq₁₋₃₊ : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → ((P  ⟫=+  Q) ⟫=+ R)  ⊑+  (P  ⟫=+  ( λ x → Q x ⟫= R  ))
  assSeq₁₋₃₊ P Q R .[] .nothing empty = empty
  assSeq₁₋₃₊ P Q R .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x            (assSeq+pp P Q R l x m x₁)
  assSeq₁₋₃₊ P Q R l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₁ (inj₁ x))   (assSeq∞pp (PI P x) Q R l m x₁)
  assSeq₁₋₃₊ P Q R l m (intc .l .m (inj₂ y) x₁) =  intc l m (inj₁ (inj₂ y))  (assPT+pp P Q R y l m x₁)
  assSeq₁₋₃₊  {c₀} {c₁} {c₂} P Q R .[] .(just (PT (P ⟫=+ (λ x → Q x ⟫= R)) x)) (terc x) = intc []
                                                                                             (just (PT (P ⟫=+ (λ x₁ → (Q x₁) ⟫= R)) x))
                                                                                                  (inj₂ x) (lemTrTerminateBind'
                                                                                                               c₀ c₁ c₂ P Q R x)

  assSeq∞pp : {c₀ c₁ c₂ : Choice} (P : Process∞ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → ((P  ⟫=∞  Q) ⟫=∞ R)  ⊑∞  (P  ⟫=∞  ( λ x → Q x ⟫= R ))
  forcet (assSeq∞pp {c₀} {c₁} {c₂} P Q R l m q) =  assSeq (forcep P) Q R l m (forcet q)


  assPT+pp : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)(Q : ChoiceSet c₀ → Process ∞ c₁)
                  → (R  : ChoiceSet c₁ → Process ∞ c₂)
                  → (y  : ChoiceSet (T P))
                  → (l  : List Label)
                  → (m  : Maybe (ChoiceSet c₂))
                  → (x : Tr∞ l m (PI (P ⟫=+ (λ x → Q x ⟫= R)) (inj₂ y)))
                  →      Tr∞ l m (PI (P ⟫=+ Q) (inj₂ y) ⟫=∞ R)
  forcet (assPT+pp {c₀} {c₁} {c₂} P Q R y l m tr) = forcet tr



  assSeq+pp : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → (l   : List Label)
                 → (x   : ChoiceSet (E P))
                 → (m   : Maybe (ChoiceSet c₂))
                 → (x₁ : Tr∞ l m (_⟫=∞_ (PE P x) (λ x₂ → _⟫=_ (Q x₂) R)))
                 → Tr∞ l m (_⟫=∞_ (_⟫=∞_ (PE P x) Q) R)
  forcet (assSeq+pp P Q R l x m x₁) = assSeq (forcep (PE P x)) Q R l m (forcet x₁)





mutual
  assSeqᵣ : {c₀ c₁ c₂ : Choice} (P : Process ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 →   (P  ⟫=  ( λ x → Q x ⟫= R  ))  ⊑  ((P  ⟫=  Q) ⟫= R)
  assSeqᵣ (terminate x) Q R l m q = q
  assSeqᵣ (node x) Q R l m q = tnode (assSeq₁₋₃₊ᵣ x Q R l m (forcet' l m q))


  assSeq₁₋₃₊ᵣ : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 →  (P  ⟫=+  ( λ x → Q x ⟫= R  ))  ⊑+ ((P  ⟫=+  Q) ⟫=+ R)
  assSeq₁₋₃₊ᵣ P Q R .[] .nothing empty = empty
  assSeq₁₋₃₊ᵣ P Q R .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (assSeq+ppᵣ P Q R l x m x₁)
  assSeq₁₋₃₊ᵣ P Q R l m (intc .l .m (inj₁ (inj₁ x)) x₁) = intc l m (inj₁ x) (assSeq∞ppᵣ (PI P x) Q R l m x₁)
  assSeq₁₋₃₊ᵣ P Q R l m (intc .l .m (inj₁ (inj₂ y)) x₁) = intc l m (inj₂ y) (assPT+ppᵣ P Q R y l m x₁)
  assSeq₁₋₃₊ᵣ P Q R l m (intc .l .m (inj₂ ()) x₁)
  assSeq₁₋₃₊ᵣ P Q R .[] .(just (PT ((P ⟫=+ Q) ⟫=+ R) _)) (terc ())


  assSeq+ppᵣ : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → (l   : List Label)
                 → (x   : ChoiceSet (E P))
                 → (m   : Maybe (ChoiceSet c₂))
                 → (x₁ :  Tr∞ l m (_⟫=∞_ (_⟫=∞_ (PE P x) Q) R))
                 →  Tr∞ l m (_⟫=∞_ (PE P x) (λ x₂ → _⟫=_ (Q x₂) R))
  forcet (assSeq+ppᵣ P Q R l x m x₁) = assSeqᵣ (forcep (PE P x)) Q R l m (forcet x₁)

  assSeq∞ppᵣ : {c₀ c₁ c₂ : Choice} (P : Process∞ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 →  (P  ⟫=∞  ( λ x → Q x ⟫= R )) ⊑∞  ((P  ⟫=∞  Q) ⟫=∞ R) 
  forcet (assSeq∞ppᵣ {c₀} {c₁} {c₂} P Q R l m q) =  assSeqᵣ (forcep P) Q R l m (forcet q)


  assPT+ppᵣ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)(Q : ChoiceSet c₀ → Process ∞ c₁)
                  → (R  : ChoiceSet c₁ → Process ∞ c₂)
                  → (y  : ChoiceSet (T P))
                  → (l  : List Label)
                  → (m  : Maybe (ChoiceSet c₂))
                  → (x : Tr∞ l m (PI (P ⟫=+ Q) (inj₂ y) ⟫=∞ R))
                  →      Tr∞ l m (PI (P ⟫=+ (λ x → Q x ⟫= R)) (inj₂ y))
  forcet (assPT+ppᵣ {c₀} {c₁} {c₂} P Q R y l m tr) =  forcet tr


≡assSeq :  {c₀ c₁ c₂ : Choice}(P : Process ∞ c₀)(Q : ChoiceSet c₀ → Process ∞ c₁)
                  → (R  : ChoiceSet c₁ → Process ∞ c₂)             
        → ((P  ⟫=  Q) ⟫= R) ≡  (P  ⟫=  ( λ x → Q x ⟫= R  ))
≡assSeq P Q R = (assSeq P Q R) , (assSeqᵣ P Q R)




