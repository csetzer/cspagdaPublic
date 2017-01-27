module proofRenamingSkip where


open import process 
open import Size
open import choiceSetU
open import label
open import TraceWithoutSize
open import RefWithoutSize
open import primitiveProcess
open import renamingOperator
open import traceEquivalence
open import Data.Product


unitRenameLaw : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Label) 
               → (P : Process i c₀)
               → Rename  A (terminate a)  ⊑ (terminate a)
unitRenameLaw a A P l m x = x



unitRenameLawᵣ : {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Label) 
               → (P : Process i c₀)
               →  (terminate a)  ⊑  Rename  A (terminate a)
unitRenameLawᵣ a A P l m x = x


≡unitRename :  {i : Size} {c₀  : Choice} (a : ChoiceSet c₀)
               → (A : Label → Label) 
               → (P : Process i c₀)
        →   Rename  A (terminate a) ≡ (terminate a)
≡unitRename a A P = (unitRenameLaw a A P) , (unitRenameLawᵣ a A P)
