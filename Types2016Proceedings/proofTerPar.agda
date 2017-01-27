module proofTerPar where 


open import process 
open import Size
open import choiceSetU
open import renamingResult
open import TraceWithoutSize
open import RefWithoutSize
open import auxData
open import label
open import parallelSimple
open import restrict
open import Data.Bool
open import traceEquivalence
open import Data.Product


unit[-||-] : {c₀ : Choice} (a : ChoiceSet c₀)(P : Process ∞ c₀) (A B : Label → Bool) 
        → (terminate a [ A ]||[ B ] P) ⊑ fmap ( (λ b → (a ,, b))) (P ↾ (B ∖ A))
unit[-||-] {c₀} a P A B l m q =  q



unit[-||-]r : {c₀ : Choice} (a : ChoiceSet c₀)(P : Process ∞ c₀) (A B : Label → Bool) 
        →  fmap ( (λ b → (a ,, b))) (P ↾ (B ∖ A)) ⊑ (terminate a [ A ]||[ B ] P)
unit[-||-]r {c₀} a P A B l m q =  q


≡U+ : {c₀ : Choice} (a : ChoiceSet c₀)(P : Process ∞ c₀) (A B : Label → Bool) 
        →  (terminate a [ A ]||[ B ] P) ≡ fmap ( (λ b → (a ,, b))) (P ↾ (B ∖ A))
≡U+  a P A B = (unit[-||-] a P A B) , (unit[-||-]r a P A B)



unit[-||-]ᵣ : {c₀ : Choice} (b : ChoiceSet c₀)(P : Process ∞ c₀) (A B : Label → Bool) 
        → (P [ B ]||[ A ] terminate b) ⊑  fmap (λ a → (a ,, b))(P ↾ (B ∖ A))

unit[-||-]ᵣ  {c₀} a (terminate x) A B l m q = q
unit[-||-]ᵣ  {c₀} a (node x) A B l m (tnode x₁) = tnode x₁


unit[-||-]ᵣᵣ : {c₀ : Choice} (b : ChoiceSet c₀)(P : Process ∞ c₀) (A B : Label → Bool) 
        →   fmap (λ a → (a ,, b))(P ↾ (B ∖ A)) ⊑ (P [ B ]||[ A ] terminate b)

unit[-||-]ᵣᵣ {c₀} a (terminate x) A B l m q = q
unit[-||-]ᵣᵣ {c₀} a (node x) A B l m (tnode x₁) = tnode x₁



≡Uᵣ+ : {c₀ : Choice} (b : ChoiceSet c₀)(P : Process ∞ c₀) (A B : Label → Bool) 
        →   (P [ B ]||[ A ] terminate b) ≡ fmap (λ a → (a ,, b))(P ↾ (B ∖ A))
≡Uᵣ+ b P A B = (unit[-||-]ᵣ b P A B) , (unit[-||-]ᵣᵣ b P A B)




ter[-||-] : {c₀ c₁ : Choice} (a : ChoiceSet c₀) (b : ChoiceSet c₁) (A  B : Label → Bool) 
        → (terminate a [ A ]||[ B ] terminate b) ⊑ fmap (λ x → a ,, b) (terminate ((a ,, b)))
ter[-||-]  {c₀} a P A B l m q =  q


ter[-||-]ᵣ : {c₀ c₁ : Choice} (a : ChoiceSet c₀) (b : ChoiceSet c₁) (A  B : Label → Bool) 
        →  fmap (λ x → a ,, b) (terminate ((a ,, b))) ⊑  (terminate a [ A ]||[ B ] terminate b)
ter[-||-]ᵣ a P A B l m q =  q


≡ter[-||-] : {c₀ c₁ : Choice} (a : ChoiceSet c₀) (b : ChoiceSet c₁) (A  B : Label → Bool) 
        →   (terminate a [ A ]||[ B ] terminate b) ≡ fmap (λ x → a ,, b) (terminate ((a ,, b)))
≡ter[-||-] a b A B = (ter[-||-] a b A B) , (ter[-||-]ᵣ a b A B)

