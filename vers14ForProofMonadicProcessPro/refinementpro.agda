
module refinementpro where



open import Size 
open import Data.List
open import Data.Product
open import Data.Maybe
open import label
open import process
open import choiceSetU
open import indTr
open import refinement
open import renamingResult

sym : {i : Size} {c : Choice} (m : Maybe (ChoiceSet c)) (P : Process i c) (Q : Process i c) → Set 
sym m P Q  = (l : List Label) → Tr l m Q → Tr l m P


reflRef : {i : Size} {c : Choice} (m : Maybe (ChoiceSet c)) (P : Process i c) → P ⊑ P 
reflRef m P  l tr tr₁ =  tr₁

--SymRef : {i : Size}{c : Choice} (P : Process i c) (Q : Process i c) →((P ⊑ Q) → (Q ⊑ P)) →  (P ⊑ Q) → (Q ⊑ P)
--SymRef P Q f PQ l trP =  f (λ l₁ x₂ → PQ l₁ x₂ ) l trP 

{-
SymRef : {i : Size}{c c₁ : Choice} (P : Process i c) (Q : Process i c₁) →((fmap {!!} P ⊑ fmap {!!} Q) → (fmap {!!} Q ⊑ fmap {!!} P)) →  (P ⊑ fmap {!!} Q) → (Q ⊑ fmap {!!} P)
SymRef P Q f PQ l trP = {!!} --  f (λ l₁ x₂ → PQ l₁ x₂ ) l trP 
-}
-- →((P ⊑ Q) → (Q ⊑ P)) →  (P ⊑ Q) → (Q ⊑ P)
--

transRef : {i : Size}{c : Choice} (P : Process i c) (Q : Process i c) (R : Process i c)  → (P ⊑ Q)  → (Q ⊑ R) → (P ⊑ R)
transRef P Q R PQ QR l m tr  = PQ l m (QR l m tr)



{-
SymRef' : {i : Size}{c : Choice} (P : Process i c) (Q : Process i c) →((P ⊑ Q) → (Q ⊑ P)) →  (P ⊑ Q) → (Q ⊑ P)
SymRef' P Q f PQ l trP = f (λ l₁ x₂ → PQ l₁ x₂ ) l trP 

-}
