module proofTerInter where 


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
open import interleave
open import traceEquivalence
open import Data.Product



TerIntLaw : {c₀ c₁  : Choice} (a : ChoiceSet c₀) (b : ChoiceSet c₁)
               → (terminate a ||| terminate b)  ⊑  terminate ((a ,, b))
TerIntLaw  {c₀} {c₁} a P l m q = q


TerIntLawᵣ : {c₀ c₁  : Choice} (a : ChoiceSet c₀) (b : ChoiceSet c₁)
               →   terminate ((a ,, b)) ⊑ (terminate a ||| terminate b)
TerIntLawᵣ {c₀} {c₁} a P l m q = q



≡TerInt+ :  {c₀ c₁  : Choice} (a : ChoiceSet c₀) (b : ChoiceSet c₁)
        →  (terminate a ||| terminate b) ≡ terminate ((a ,, b))
≡TerInt+ a b = TerIntLaw a b , TerIntLawᵣ a b



uniIntLaw : {c₀  : Choice} (a : ChoiceSet c₀) 
               → (P : Process ∞ c₀)
               → (terminate a ||| P)  ⊑ fmap ((_,,_ a)) P
uniIntLaw {c₀} a P l m q = q


uniIntLawᵣ : {c₀  : Choice} (a : ChoiceSet c₀) 
               → (P : Process ∞ c₀)
               →  fmap ((_,,_ a)) P  ⊑  (terminate a ||| P)
uniIntLawᵣ {c₀} a P l m q = q


≡uniInt :  {c₀  : Choice} (a : ChoiceSet c₀) 
               → (P : Process ∞ c₀)         
        →   (terminate a ||| P) ≡ fmap ((_,,_ a)) P
≡uniInt a P = (uniIntLaw a P) , (uniIntLawᵣ a P)

