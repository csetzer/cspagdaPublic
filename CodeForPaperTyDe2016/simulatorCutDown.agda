module simulatorCutDown where


open import Size
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import ooAgda.SizedIO.Base  renaming (force to forceIO; delay to delayIO)
open import ooAgda.SizedIO.Console hiding (main)
open import ooAgda.NativeIO 
open import choiceSetU
open import process 
open Process∞
open Process+
open import showFunction
open import choiceAuxFunction
open import label
open import preFix
open import primitiveProcess
open import interleave


mutual
   simulator : ∀ {i} → {c₀ : Choice} 
            → Process ∞ c₀ → IOConsole i Unit
   forceIO (simulator P) = 
      do' (putStrLn (Str P))                 λ _  → 
      do  (putStrLn ("Termination-Events:" 
                     ++s showTicks P))       λ _  → 
      do  (putStrLn 
             ("Events" ++s showLabels₁ P))   λ _  → 
      do  (putStrLn ("Choose Event"))        λ _  → 
      do  getLine                            λ s  → 
      simulator₁ P  (lookupChoice 
                    (processToE P) (processToI P) s)

   simulator₁ : ∀ {i} → {c₀ : Choice} 
               → (P : Process ∞ c₀) 
               → Maybe ((ChoiceSet (processToE P)) 
                      ⊎ (ChoiceSet (processToI P)))
               → IOConsole i Unit  
   forceIO (simulator₁ P nothing) = 
      do' (putStrLn
        "please enter a choice amongst")     λ _ →  
      do (putStrLn (showLabels₁ P))          λ _ →  
      simulator P
   simulator₁ P (just c₁) = 
      simulator (processToSubprocess P c₁)

setSTOP : Choice
setSTOP = namedElements ("STOP" ∷ [])

transition₁ : ∀ i → Process i setSTOP
transition₁  i = laba ⟶ delay (labb ⟶ delay (labc ⟶ delay (STOP {∞} setSTOP )))

transition₂ : ∀ i → Process i setSTOP
transition₂  i = laba ⟶ delay (labb ⟶ delay (labc ⟶ delay {↑ (↑ i)} (STOP {∞} setSTOP )))

myResultType : Choice
myResultType = setSTOP ×' setSTOP

myProcess :  Process ∞ myResultType
myProcess = transition₁ ∞  ||| transition₂ ∞ 

main  : NativeIO Unit 
main = translateIOConsole (simulator myProcess)

