module internalChoice where 


open import Size
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import Data.List.Base renaming (map to mapL)
open import choiceSetU
open import process
open import showFunction
open import dataAuxFunction
open Process+
open Process∞





funcChoice2ProcessToProcess₁ : ∀ {i} → {c₀ : Choice} → (c : Choice) → (ChoiceSet c  → Process i (ChoiceSet c₀)) → String
funcChoice2ProcessToProcess₁ {i} {c₀} c f = unlines (mapL ((λ x → "(λ "  ++s (choice2String c x) ++s " → " ++s showProcess c₀ (f x) ++s ")")) (choice2Enumeration0 c))


funcChoice2ProcessToProcess₁∞ : ∀ {i}  → {c₀ : Choice} → (c : Choice) → (ChoiceSet c  → Process∞ (↑ i)  (ChoiceSet c₀)) → String
funcChoice2ProcessToProcess₁∞ {i} c f = funcChoice2ProcessToProcess₁ c (λ x → forcep (f x ) i )


mutual
  IntChoice∞ : (i : Size) → {c₀ : Choice} → (c : Choice) 
          → (PI : ChoiceSet c → Process∞ i (ChoiceSet c₀)) 
          → Process∞ i (ChoiceSet c₀)  
  forcep (IntChoice∞ i c PI) j = IntChoice i c PI

  IntChoice : (i : Size) → {c₀ : Choice} → (c : Choice) 
          → (PI : ChoiceSet c → Process∞ i (ChoiceSet c₀)) 
          → Process i (ChoiceSet c₀)  
  IntChoice i c PI = node (IntChoice+ i c PI)

  IntChoice+ : (i : Size) → {c₀ : Choice} → (c : Choice) 
          → (PI : ChoiceSet c → Process∞ i (ChoiceSet c₀)) 
          → Process+ i (ChoiceSet c₀)  
  E   (IntChoice+ i {c₀} c P)    = fin 0
  Lab (IntChoice+ i {c₀} c P)    = efq 
  PE  (IntChoice+ i {c₀} c P)    = efq 
  I   (IntChoice+ i {c₀} c P)    = {!!}
  PI  (IntChoice+ i {c₀} c P)    = {!!}
  Str (IntChoice+ i {c₀} c P)    = (" \t ⊔ \t " ++s {!!})  

--node (fin 0) efq efq c PI (" \t ∪ \t " ++s funcChoice2ProcessToProcess₁∞ c PI) 



