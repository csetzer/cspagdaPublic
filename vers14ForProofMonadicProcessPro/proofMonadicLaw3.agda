{-# OPTIONS --show-implicit #-}

module proofMonadicLaw3 where 

open import process 
open import indTr
open Tr∞
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
open import refinement
open import sequentialCompositionRev
open import refinementpro
open import renamingResult






lemTrTerminateBind : (i : Size)(c : Choice)(P : Process+ i c)(x : ChoiceSet (T P))
                     → Tr∞ [] (just (PT P x)) (PI (P ⟫=+ terminate) (inj₂ x))
forcet (lemTrTerminateBind i c P x) = ter (PT P x)


lemTrTerminateBind' : (i : Size)(c₀ c₁ c₂ : Choice)
                      (P : Process+ i c₀)
                      (Q : ChoiceSet c₀ → Process i c₁)
                      (R : ChoiceSet c₁ → Process i c₂)
                      (x  : Fin 0)
                     → Tr∞ [] (just (PT (_⟫=+_ P (λ x₁ → _⟫=_ (Q x₁) R)) x))(PI (_⟫=+_ (_⟫=+_ P Q) R) (inj₂ x))
forcet (lemTrTerminateBind' i c P Q R x q ()) {j}


mutual
  monadicLaw₁₋₃ : {i : Size} {c₀ c₁ c₂ : Choice} (P : Process i c₀)
                 (Q : ChoiceSet c₀ → Process i c₁)
                 (R : ChoiceSet c₁ → Process i c₂)
                 → ((P  ⟫=  Q) ⟫= R)  ⊑  (P  ⟫=  ( λ x → Q x ⟫= R  ))
  monadicLaw₁₋₃ {i} {c₀} {c₁} {c₂} (terminate x) Q R l m q = q
  monadicLaw₁₋₃ {i} {c₀} {c₁} {c₂} (node x) Q R l m q = tnode (monadicLaw₁₋₃₊ x Q R l m (forcet' l m q))


  monadicLaw₁₋₃₊ : {i : Size} {c₀ c₁ c₂ : Choice} (P : Process+ i c₀)
                 (Q : ChoiceSet c₀ → Process i c₁)
                 (R : ChoiceSet c₁ → Process i c₂)
                 → ((P  ⟫=+  Q) ⟫=+ R)  ⊑+  (P  ⟫=+  ( λ x → Q x ⟫= R  ))
  monadicLaw₁₋₃₊ P Q R .[] .nothing empty = empty
  monadicLaw₁₋₃₊ P Q R .(Lab P x ∷ l) m (extc l .m x x₁) = extc l m x (monadicLaw∞ P Q R l x m x₁) -- (monadicLaw₁₋₃∞ (PE P x) Q R l m x₁)
  monadicLaw₁₋₃₊ P Q R l m (intc .l .m (inj₁ x) x₁) = intc l m (inj₁ (inj₁ x)) (monadicLaw₁₋₃∞ (PI P x) Q R l m x₁)
  monadicLaw₁₋₃₊ {i} {c₀} {c₁} {c₂} P Q R l m (intc .l .m (inj₂ y) x₁) =  intc l m (inj₁ (inj₂ y))  (monadPT+ P Q R y l m x₁)
  monadicLaw₁₋₃₊ {i} {c₀} {c₁} {c₂} P Q R .[] .(just (PT (P ⟫=+ (λ x → Q x ⟫= R)) x)) (terc x) = intc [] (just (PT (_⟫=+_  P (λ x₁ → _⟫=_ (Q x₁) R)) x))  (inj₂ x) (lemTrTerminateBind' i c₀ c₁ c₂ P Q R x)

  monadicLaw₁₋₃∞ : {i : Size} {c₀ c₁ c₂ : Choice} (P : Process∞ i c₀)
                 (Q : ChoiceSet c₀ → Process i c₁)
                 (R : ChoiceSet c₁ → Process i c₂)
                 → ((P  ⟫=∞  Q) ⟫=∞ R)  ⊑∞  (P  ⟫=∞  ( λ x → Q x ⟫= R ))
  forcet (monadicLaw₁₋₃∞ {i} {c₀} {c₁} {c₂} P Q R l m q) {j} =  monadicLaw₁₋₃ (forcep P) Q R l m {!!} --(forcet {!q!})

  fLaw₁₋₃∞ : {i : Size} {c₀ c₁ c₂ : Choice} (P : Process+ i c₀)
                 (Q : ChoiceSet c₀ → Process i c₁)
                 (R : ChoiceSet c₁ → Process i c₂)
                 →  (y : ChoiceSet (T P))
                 → (PI (P ⟫=+ Q) (inj₂ y) ⟫=∞ R)   ⊑∞ ((PI (P ⟫=+ (λ x → Q x ⟫= R)) (inj₂ y)))
  forcet (fLaw₁₋₃∞ {i} {c₀} {c₁} {c₂} P Q R y l m x) {j} = {!!}



  monadicLaw∞ : {i : Size} {c₀ c₁ c₂ : Choice} (P : Process+ i c₀)
                 (Q : ChoiceSet c₀ → Process i c₁)
                 (R : ChoiceSet c₁ → Process i c₂)
                 → (l   : List Label)
                 → (x   : ChoiceSet (E P))
                 → (m   : Maybe (ChoiceSet c₂))
                 → (x₁ : Tr∞ {i} {c₂} l m (_⟫=∞_ {i} {c₀} {c₂} (PE P x) (λ x₂ → _⟫=_ {i} {c₁} {c₂} (Q x₂) R)))
                 → Tr∞ {i} {c₂} l m (_⟫=∞_ {i} {c₁} {c₂} (_⟫=∞_ {i} {c₀}{c₁} (PE P x) Q) R)
  forcet (monadicLaw∞ {i} {c₀} {c₁} {c₂} P Q R l x m x₁) {j} = monadicLaw₁₋₃ (forcep (PE P x)) Q R l m {!!} 


  monadPT+ : {i : Size}{c₀ c₁ c₂ : Choice}(P : Process+ i c₀)(Q : ChoiceSet c₀ → Process i c₁)
                  → (R  : ChoiceSet c₁ → Process i c₂)
                  → (y  : ChoiceSet (T P))
                  → (l  : List Label)
                  → (m  : Maybe (ChoiceSet c₂))
                  → (x : Tr∞ l m (PI (P ⟫=+ (λ x → Q x ⟫= R)) (inj₂ y)))
                  →      Tr∞ l m (PI (P ⟫=+ Q) (inj₂ y) ⟫=∞ R)
  forcet (monadPT+ {i} {c₀} {c₁} {c₂} P Q R y l m tr) {j} = {!!}


  monadPT : {i : Size}{j : Size< i}{c₀ c₁ c₂ : Choice} (P : Process i c₀)(Q : ChoiceSet c₀ → Process i c₁)
                  → (R  : ChoiceSet c₁ → Process i c₂)
                  → (l   : List Label)
                  → (m   : Maybe (ChoiceSet c₂))
                  → Tr l m (P ⟫= (λ x → (_⟫=_ {j} (Q x) R)))
                  → Tr l m ((P ⟫= (λ x → (_⟫=_ {i} (Q x) R))))
  monadPT {i} {j} {c₀} {c₁} {c₂} P Q R l m x₁ = {!!}



  monadDownSize : (i : Size)(j : Size< i)(c₀ c₁ : Choice) (P : Process i c₀)(Q : ChoiceSet c₀ → Process i c₁)
                  → (l   : List Label)
                  → (m   : Maybe (ChoiceSet c₁))
                  → Tr {j} {c₁} l m (_⟫=_ {i} {c₀} {c₁} P  Q)
                  → Tr {j} {c₁} l m (_⟫=_ {j} {c₀} {c₁} P  Q)
  monadDownSize i j c₀ c₁ (terminate x) Q l m tr = tr
  monadDownSize i j c₀ c₁ (node x) Q l m (tnode {l = .l} {x = .m} {P = .(_⟫=+_ {i} {c₀} {c₁} x Q)} x₁) = tnode (monadDownSize+ i j c₀ c₁ x Q l m x₁)



  monadDownSize+ : (i : Size)(j : Size< i)(c₀ c₁ : Choice) (P : Process+ i c₀)(Q : ChoiceSet c₀ → Process i c₁)
                  → (l   : List Label)
                  → (m   : Maybe (ChoiceSet c₁))
                  → Tr+ {j} {c₁} l m (_⟫=+_ {i} {c₀} {c₁} P  Q)
                  → Tr+ {j} {c₁} l m (_⟫=+_ {j} {c₀} {c₁} P  Q)
  monadDownSize+ i j c₀ c₁ q P .[] .nothing (empty {P = .(_⟫=+_ {i} {c₀} {c₁} q P)}) = empty
  monadDownSize+ i j c₀ c₁ q P .(Lab q x ∷ l) m (extc {P = .(_⟫=+_ {i} {c₀} {c₁} q P)} l .m x x₁) = extc l m x (monadDownSize∞ i j c₀ c₁ (PE q x) P l m x₁)
  monadDownSize+ i j c₀ c₁ q P l m (intc {P = .(_⟫=+_ {i} {c₀} {c₁} q P)} .l .m (inj₁ x) x₁) = intc l m (inj₁ x) (monadDownSize∞ i j c₀ c₁ (PI q x) P l m x₁)
  monadDownSize+ i j c₀ c₁ q P l m (intc {P = .(_⟫=+_ {i} {c₀} {c₁} q P)} .l .m (inj₂ y) x₁)  = intc l m (inj₂ y) (monadDownSizePT i j c₀ c₁ q P y l m x₁)
  monadDownSize+ i j c₀ c₁ q P .[] .(just (PT (_⟫=+_ {i} {c₀} {c₁} q P) x)) (terc {P = .(_⟫=+_ {i} {c₀} {c₁} q P)} x) = efq x


  monadDownSizePT : (i : Size)(j : Size< i)(c₀ c₁ : Choice) (P : Process+ i c₀)(Q : ChoiceSet c₀ → Process i c₁)
                  → (y  : ChoiceSet (T P))
                  → (l   : List Label)
                  → (m   : Maybe (ChoiceSet c₁))
                  → Tr∞ {j} {c₁} l m (PI (_⟫=+_ {i} {c₀} {c₁} P Q) (inj₂ y))
                  → Tr∞ {j} {c₁} l m (PI (_⟫=+_ {j} {c₀} {c₁} P Q) (inj₂ y))
  forcet (monadDownSizePT i j c₀ c₁ P Q y l m tr) = forcet tr                  


  monadDownSize∞ : (i : Size)(j : Size< i)(c₀ c₁ : Choice) (P : Process∞ i c₀)(Q : ChoiceSet c₀ → Process i c₁)
                  → (l   : List Label)
                  → (m   : Maybe (ChoiceSet c₁))
                  → Tr∞ {j} {c₁} l m (_⟫=∞_ {i} {c₀} {c₁} P  Q)
                  → Tr∞ {j} {c₁} l m (_⟫=∞_ {j} {c₀} {c₁} P  Q)
  forcet (monadDownSize∞ i j c₀ c₁ P Q l m tr) {j'} =  forcet {j} tr



{-
Goal: Tr∞ {.i} {.c₂} l m (_⟫=∞_ {.i} {.c₁} {.c₂} (_⟫=∞_ {.i} {.c₀} {.c₁} (PE P x) Q) R)
————————————————————————————————————————————————————————————
x₁  : Tr∞ {.i} {.c₂} l m (_⟫=∞_ {.i} {.c₀} {.c₂} (PE P x)(λ x₂ → _⟫=_ {.i} {.c₁} {.c₂} (Q x₂) R))
m   : Maybe {Level.zero} (ChoiceSet .c₂)
x   : ChoiceSet (E P)
l   : List {Level.zero} Label
R   : ChoiceSet .c₁ → Process .i .c₂
Q   : ChoiceSet .c₀ → Process .i .c₁
P   : Process+ .i .c₀
.c₁ : Choice
.c₀ : Choice
.i  : Size
.c₂ : Choice
-}


-- Goal: Tr {j} {c₂} l m (_⟫=_ {j} {c₁} {c₂} (Q (PT P y)) R)
-- Have: Tr {j} {c₂} l m (_⟫=_ {i} {c₁} {c₂} (Q (PT P y)) R)

-- → (x : Tr∞ l m (PI (P ⟫=+ (λ x → Q x ⟫= R)) (inj₂ y)))
-- →  Tr∞ l m (PI (P ⟫=+ Q) (inj₂ y) ⟫=∞ R)
-- forcet (fLaw₁₋₃∞ {i} {c₀} {c₁} {c₂} P Q R y l m x) {j} =  {!forcep (PI (P ⟫=+ Q) (inj₂ y) ⟫=∞ R) {j} !}  -- forcet x


{-

forcep (PI (P ⟫=+ (λ x → Q x ⟫= R)) (inj₂ y)) {j} = Q (PT P y) ⟫= R
forcep (PI (P ⟫=+ Q) (inj₂ y) ⟫=∞ R) {j}           = Q (PT P y) ⟫= R

Goal: Tr∞ l m (PI (P ⟫=+ Q) (inj₂ y) ⟫=∞ R)
Have: Tr∞ l m (PI (P ⟫=+ (λ x → Q x ⟫= R)) (inj₂ y))
————————————————————————————————————————————————————————————
x₁  : Tr∞ l m (PI (P ⟫=+ (λ x → Q x ⟫= R)) (inj₂ y))
y   : ChoiceSet (T P)
R   : ChoiceSet .c₁ → Process .i .c₂
Q   : ChoiceSet .c₀ → Process .i .c₁
P   : Process+ .i .c₀
.c₁ : Choice
.c₀ : Choice
.i  : Size
m   : Maybe (ChoiceSet .c₂)
.c₂ : Choice
l   : List Label
-}



--Goal: Tr∞ l m (PI (P ⟫=+ Q) (inj₂ y) ⟫=∞ R)
--Have: Tr∞ l m (PI (P ⟫=+ (λ x → Q x ⟫= R)) (inj₂ y))


-- monadicLaw₁₋₃₊ P Q R l m (intc {P = .(_⟫=+_ P (λ x₂ → _⟫=_ (Q x₂) R))} .l .m (inj₂ y) x₁) = {!!}
-- monadicLaw₁₋₃₊ P Q R l m (intc .l .m (inj₂ y) x₁) = intc l m (inj₂ {!y!}) {!!}
-- monadicLaw₁₋₃₊ P Q R l m (forcet' l m (forcet x₁))
-- forcet' [] (just (PT (P ⟫=+ (λ x₁ → Q x₁ ⟫= R)) x)) (tnode {!terc!}) 
-- intc [] (just (PT (P ⟫=+ (λ x₁ → Q x₁ ⟫= R)) x)) {!!} (monadicLaw₁₋₃∞ {!!} {!!} {!!} [] (just (PT (P ⟫=+ (λ x₁ → Q x₁ ⟫= R)) x)) {!!})
-- intc l m {!!} (monadicLaw₁₋₃∞ {!!} {!!} {!!} l m {!d!})












