{-# OPTIONS --show-implicit #-}

module proofMonadicLaw where 

open import process 
open import Size
open import Level
open import choiceSetU
open import auxData
open import Data.Maybe
open import Data.Product
open import Data.Nat
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
open import traceEquivalence




lemTrTerminateBind : (c : Choice)(P : Process+ ∞ c)(x : ChoiceSet (T P))
                     → Tr∞ [] (just (PT P x)) (PI (P ⟫=+ terminate) (inj₂ x))
forcet (lemTrTerminateBind  c P x) = ter (PT P x)



lemTrTerminateBind'' : (c : Choice)(P : Process+ ∞ c) (x : Fin 0)
                     → Tr+ [] (just (PT (P ⟫=+ terminate) x)) P
lemTrTerminateBind'' c P ()



lemTrTerminateBind' : (c₀ c₁ c₂ : Choice)
                      (P : Process+ ∞ c₀)
                      (Q : ChoiceSet c₀ → Process ∞ c₁)
                      (R : ChoiceSet c₁ → Process ∞ c₂)
                      (x  : Fin 0)
                     → Tr∞ [] (just (PT (_⟫=+_ P (λ x₁ → _⟫=_ (Q x₁) R)) x))(PI (_⟫=+_ (_⟫=+_ P Q) R) (inj₂ x))
forcet (lemTrTerminateBind'  c P Q R x q ())


lemTrTerminateBind''' : {c₀ c₁ c₂ : Choice}
                      (P : Process+ ∞ c₀)
                      (Q : ChoiceSet c₀ → Process ∞ c₁)
                      (R : ChoiceSet c₁ → Process ∞ c₂)
                      (x  : Fin 0)
                     →  Tr+ [](just (PT ((P ⟫=+ Q) ⟫=+ R) x))(P ⟫=+ (λ x₁ → (Q x₁) ⟫= R))
lemTrTerminateBind''' P Q R ()


--"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""--

monadicLaw₁ : {c₀ c₁  : Choice} (a : ChoiceSet c₀)(P : ChoiceSet c₀ → Process ∞ c₁)
               → (terminate a ⟫= P)  ⊑  P a
monadicLaw₁  a P l m q = q

monadicLaw₁ᵣ : {c₀ c₁  : Choice} (a : ChoiceSet c₀)(P : ChoiceSet c₀ → Process ∞ c₁)
               → P a ⊑ (terminate a ⟫= P)
monadicLaw₁ᵣ {c₀} {c₁} a P l m q = q

≡monadicLaw₁ : {c₀ c₁ : Choice} (a : ChoiceSet c₀)(P : ChoiceSet c₀ → Process ∞ c₁)
        → (P a) ≡  (terminate a ⟫= P)
≡monadicLaw₁ {c₀} {c₁} a P = (monadicLaw₁ a P) , (monadicLaw₁ᵣ a P)





--"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""--


mutual
  monadicLaw₂ : {c₀  : Choice} (P : Process ∞ c₀)
                 → (P  ⟫=  terminate)  ⊑  P
  monadicLaw₂ {c₀} (terminate x) l m q = q
  monadicLaw₂ {c₀} (node x) l m q = tnode (monadicLaw₂₊ x l m (forcet' l m q))


  monadicLaw₂₊ : {c₀  : Choice} (P : Process+ ∞ c₀)
                 → (P  ⟫=+  terminate)  ⊑+  P
  monadicLaw₂₊  {c₀} P .[] .nothing empty = empty
  monadicLaw₂₊  {c₀} P .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (monadicLaw₂∞ (PE P x) l m x₁)
  monadicLaw₂₊  {c₀} P l m (intc .l .m x x₁) =  intc l m (inj₁ x) (monadicLaw₂∞ (PI P x) l m x₁)
  monadicLaw₂₊  {c₀} P .[] .(just (PT P x)) (terc x) = intc [] (just (PT P x)) (inj₂ x) (lemTrTerminateBind  c₀ P x)


  monadicLaw₂∞ : {c₀  : Choice} (P : Process∞ ∞ c₀)
                 → (P  ⟫=∞  terminate)  ⊑∞  P
  forcet (monadicLaw₂∞ {c₀} P l m q) = monadicLaw₂ (forcep P) l m (forcet q)


lemtr+trterminate : (c₀ : Choice) → (m : Maybe (ChoiceSet c₀)) → (P : Process+ ∞ c₀) → (l : List Label) →
                    (y : ChoiceSet (T P)) → (traux : Tr {c₀} l m (terminate (PT P y))) → Tr+ {c₀} l m P
lemtr+trterminate c₀ .(just (PT P y)) P .[] y (ter .(PT P y)) = terc y
lemtr+trterminate c₀ .nothing P .[] y (empty .(PT P y)) = empty

mutual
  monadicLaw₂ᵣ : {c₀  : Choice} (P : Process ∞ c₀)
                 → P ⊑  (P  ⟫=  terminate)
  monadicLaw₂ᵣ {c₀} (terminate x) l m x₁ = x₁
  monadicLaw₂ᵣ {c₀} (node x) l m x₁ = tnode (monadicLaw₂ᵣ₊ x l m (forcet' l m x₁))

  monadicLaw₂ᵣ₊ : {c₀  : Choice} (P : Process+ ∞ c₀)
                 → P ⊑+  (P  ⟫=+  terminate)
  monadicLaw₂ᵣ₊ P .[] .nothing (empty {P = .(P ⟫=+ terminate)}) = empty
  monadicLaw₂ᵣ₊ P .(Lab P x ∷ l) m (extc {P = .(P ⟫=+ terminate)} l .m x x₁) = extc l m x (monadicLaw₂ᵣ∞ (PE P x) l m x₁)
  monadicLaw₂ᵣ₊ {c₀} P l m (intc {P = .(_⟫=+_ {∞} {c₀} {c₀} P terminate)} .l .m (inj₁ x) x₁) = intc l m x (monadicLaw₂ᵣ∞ (PI P x) l m x₁)
  monadicLaw₂ᵣ₊ {c₀} P l m (intc {P = .(_⟫=+_ {∞} {c₀} {c₀} P terminate)} .l .m (inj₂ y) x₁) =
       let
          s : Set
          s = Tr {c₀} l m  (forcep (PI (_⟫=+_ {∞} {c₀} {c₀} P terminate) (inj₂ y)) {∞})

          traux : Tr {c₀} l m (terminate (PT P y))
          traux = forcet x₁
          
       in lemtr+trterminate c₀ m P l y traux --  intc l m ? (monadicLaw₂ᵣ∞ (PI P ?) l m x₁)
  monadicLaw₂ᵣ₊ {c₀} P .[] .(just (PT (P ⟫=+ terminate) x)) (terc {P = .(P ⟫=+ terminate)} x) = lemTrTerminateBind'' c₀ P x

  monadicLaw₂ᵣ∞ : {c₀  : Choice} (P : Process∞ ∞ c₀)
                 → P ⊑∞  (P  ⟫=∞  terminate)
  forcet (monadicLaw₂ᵣ∞ {c₀} P l m x) = monadicLaw₂ᵣ (forcep P {∞}) l m (forcet x)




≡monadicLaw₂ : {c₀ c₁ : Choice} (P : Process ∞ c₀)
        →  P  ≡  (P  ⟫= terminate)
≡monadicLaw₂ {c₀} {c₁} P = (monadicLaw₂ᵣ P) , (monadicLaw₂ P)


--"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""--



mutual
  monadicLaw₁₋₃ : {c₀ c₁ c₂ : Choice} (P : Process ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → ((P  ⟫=  Q) ⟫= R)  ⊑  (P  ⟫=  ( λ x → Q x ⟫= R  ))
  monadicLaw₁₋₃ {c₀} {c₁} {c₂} (terminate x) Q R l m q = q
  monadicLaw₁₋₃ {c₀} {c₁} {c₂} (node x) Q R l m q = tnode (monadicLaw₁₋₃₊ x Q R l m (forcet' l m q))


  monadicLaw₁₋₃₊ : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → ((P  ⟫=+  Q) ⟫=+ R)  ⊑+  (P  ⟫=+  ( λ x → Q x ⟫= R  ))
  monadicLaw₁₋₃₊ P Q R .[] .nothing empty = empty
  monadicLaw₁₋₃₊ P Q R .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (monadicLaw∞ P Q R l x m x₁)
  monadicLaw₁₋₃₊ P Q R l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₁ (inj₁ x)) (monadicLaw₁₋₃∞ (PI P x) Q R l m x₁)
  monadicLaw₁₋₃₊ P Q R l m (intc .l .m (inj₂ y) x₁) =  intc l m (inj₁ (inj₂ y))  (monadPT+ P Q R y l m x₁)
  monadicLaw₁₋₃₊  {c₀} {c₁} {c₂} P Q R .[] .(just (PT (P ⟫=+ (λ x → Q x ⟫= R)) x)) (terc x) = intc []
                                                                                                 (just (PT(P ⟫=+ (λ x₁ → (Q x₁) ⟫= R)) x))                                                                                                      (inj₂ x) (lemTrTerminateBind'
                                                                                                                       c₀ c₁ c₂ P Q R x)

  monadicLaw₁₋₃∞ : {c₀ c₁ c₂ : Choice} (P : Process∞ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → ((P  ⟫=∞  Q) ⟫=∞ R)  ⊑∞  (P  ⟫=∞  ( λ x → Q x ⟫= R ))
  forcet (monadicLaw₁₋₃∞ {c₀} {c₁} {c₂} P Q R l m q) =  monadicLaw₁₋₃ (forcep P) Q R l m (forcet q)


  monadPT+ : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)(Q : ChoiceSet c₀ → Process ∞ c₁)
                  → (R  : ChoiceSet c₁ → Process ∞ c₂)
                  → (y  : ChoiceSet (T P))
                  → (l  : List Label)
                  → (m  : Maybe (ChoiceSet c₂))
                  → (x : Tr∞ l m (PI (P ⟫=+ (λ x → Q x ⟫= R)) (inj₂ y)))
                  →      Tr∞ l m (PI (P ⟫=+ Q) (inj₂ y) ⟫=∞ R)
  forcet (monadPT+ {c₀} {c₁} {c₂} P Q R y l m tr) = forcet tr


 
  monadDownSize : (c₀ c₁ : Choice) (P : Process ∞ c₀)(Q : ChoiceSet c₀ → Process ∞ c₁)
                  → (l   : List Label)
                  → (m   : Maybe (ChoiceSet c₁))
                  → Tr l m (_⟫=_ P  Q)
                  → Tr l m (_⟫=_ P  Q)
  monadDownSize c₀ c₁ (terminate x) Q l m tr = tr
  monadDownSize c₀ c₁ (node x) Q l m (tnode x₁) = tnode (monadDownSize+ c₀ c₁ x Q l m x₁)



  monadDownSize+ : (c₀ c₁ : Choice) (P : Process+ ∞ c₀)(Q : ChoiceSet c₀ → Process ∞ c₁)
                  → (l   : List Label)
                  → (m   : Maybe (ChoiceSet c₁))
                  → Tr+ l m (_⟫=+_ P  Q)
                  → Tr+ l m (_⟫=+_ P  Q)
  monadDownSize+ c₀ c₁ q P .[] .nothing empty = empty
  monadDownSize+ c₀ c₁ q P .(Lab q x ∷ l) m (extc l .m x x₁) =   extc l m x (monadDownSize∞ c₀ c₁ (PE q x) P l m x₁)
  monadDownSize+ c₀ c₁ q P l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₁ x) (monadDownSize∞ c₀ c₁ (PI q x) P l m x₁)
  monadDownSize+ c₀ c₁ q P l m (intc .l .m (inj₂ y) x₁) = intc l m (inj₂ y) (monadDownSizePT c₀ c₁ q P y l m x₁)
  monadDownSize+ c₀ c₁ q P .[] .(just (PT (_⟫=+_  q P) x)) (terc x) = efq x


  monadDownSizePT : (c₀ c₁ : Choice) (P : Process+ ∞ c₀)(Q : ChoiceSet c₀ → Process ∞ c₁)
                  → (y  : ChoiceSet (T P))
                  → (l   : List Label)
                  → (m   : Maybe (ChoiceSet c₁))
                  → Tr∞ l m (PI (_⟫=+_ P Q) (inj₂ y))
                  → Tr∞ l m (PI (_⟫=+_ P Q) (inj₂ y))
  forcet (monadDownSizePT c₀ c₁ P Q y l m tr) = forcet tr                  


  monadDownSize∞ : (c₀ c₁ : Choice) (P : Process∞ ∞ c₀)(Q : ChoiceSet c₀ → Process ∞ c₁)
                  → (l   : List Label)
                  → (m   : Maybe (ChoiceSet c₁))
                  → Tr∞ l m (_⟫=∞_ P  Q)
                  → Tr∞ l m (_⟫=∞_ P  Q)
  forcet (monadDownSize∞ c₀ c₁ P Q l m tr) =  forcet tr


  monadicLaw∞ : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 → (l   : List Label)
                 → (x   : ChoiceSet (E P))
                 → (m   : Maybe (ChoiceSet c₂))
                 → (x₁ : Tr∞ l m (_⟫=∞_ (PE P x) (λ x₂ → _⟫=_ (Q x₂) R)))
                 → Tr∞ l m (_⟫=∞_ (_⟫=∞_ (PE P x) Q) R)
  forcet (monadicLaw∞ P Q R l x m x₁) = monadicLaw₁₋₃ (forcep (PE P x)) Q R l m (forcet x₁)




mutual
  monadicLaw₃ᵣ : {c₀ c₁ c₂ : Choice} (P : Process ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 →  (P  ⟫=  ( λ x → Q x ⟫= R  ))   ⊑   ((P  ⟫=  Q) ⟫= R)
  monadicLaw₃ᵣ {c₀} {c₁} {c₂} (terminate x) Q R l m x₁ = x₁
  monadicLaw₃ᵣ {c₀} {c₁} {c₂} (node x) Q R l m x₁ =  tnode (monadicLaw₃ᵣ₊ x Q R l m (forcet' l m x₁))

  monadicLaw₃ᵣ₊ : {c₀ c₁ c₂ : Choice} (P : Process+ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 →  (P  ⟫=+  ( λ x → Q x ⟫= R  )) ⊑+ ((P  ⟫=+  Q) ⟫=+ R) 
  monadicLaw₃ᵣ₊ P Q R .[] .nothing empty = empty
  monadicLaw₃ᵣ₊ P Q R .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (monadicLaw₃ᵣ∞ (PE P x) Q R l m x₁)
  monadicLaw₃ᵣ₊ P Q R l m (intc .l .m (inj₁ (inj₁ x)) x₁) = intc l m (inj₁ x) (monadicLaw₃ᵣ∞ (PI P x) Q R l m x₁)
  monadicLaw₃ᵣ₊ P Q R l m (intc .l .m (inj₁ (inj₂ y)) x₁) = intc l m (inj₂ y) (monadPT+' P Q R y l m x₁)
  monadicLaw₃ᵣ₊ P Q R l m (intc .l .m (inj₂ ()) x₁)
  monadicLaw₃ᵣ₊ P Q R .[] .(just (PT (_⟫=+_ (P ⟫=+ Q) R) x)) (terc x) = lemTrTerminateBind''' P Q R x


  monadicLaw₃ᵣ∞ : {c₀ c₁ c₂ : Choice} (P : Process∞ ∞ c₀)
                 (Q : ChoiceSet c₀ → Process ∞ c₁)
                 (R : ChoiceSet c₁ → Process ∞ c₂)
                 →  (P  ⟫=∞  ( λ x → Q x ⟫= R )) ⊑∞ ((P  ⟫=∞  Q) ⟫=∞ R)
  forcet (monadicLaw₃ᵣ∞ {c₀} {c₁} {c₂} P Q R l m q) = monadicLaw₃ᵣ (forcep P) Q R l m (forcet q)


  monadPT+' : {c₀ c₁ c₂ : Choice}(P : Process+ ∞ c₀)(Q : ChoiceSet c₀ → Process ∞ c₁)
                  → (R  : ChoiceSet c₁ → Process ∞ c₂)
                  → (y  : ChoiceSet (T P))
                  → (l  : List Label)
                  → (m  : Maybe (ChoiceSet c₂))
                  → (x :  Tr∞ l m (_⟫=∞_ (PI (_⟫=+_ P Q) (inj₂ y)) R))
                  →      Tr∞ l m (PI (_⟫=+_ P (λ x → _⟫=_ (Q x) R)) (inj₂ y))
  forcet (monadPT+' {c₀} {c₁} {c₂} P Q R y l m tr) = forcet tr



≡monadicLaw₃ : {c₀ c₁ c₂ : Choice} (P : Process ∞ c₀) (Q : ChoiceSet c₀ → Process ∞ c₁) (R : ChoiceSet c₁ → Process ∞ c₂)
        →  ((P  ⟫=  Q) ⟫= R)  ≡  (P  ⟫=  ( λ x → Q x ⟫= R  ))
≡monadicLaw₃ {c₀} {c₁} {c₂} P Q R = (monadicLaw₁₋₃ P Q R) ,  (monadicLaw₃ᵣ P Q R)


--"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""--
