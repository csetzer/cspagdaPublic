module simulatorCutDown where


open import Size
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import SizedIO.Base  renaming (force to forceIO; delay to delayIO)
open import SizedIO.Console hiding (main)
open import NativeIO 
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
               → Process ∞  c₀  
               → IOConsole i Unit  
   forceIO (simulator P) = 
             do' (putStrLn (Str P))           λ _ → 
             do (putStrLn (showProLab P))    λ _ → 
             do (putStrLn ("Enter a choice")) λ _ → 
             do getLine                       λ s → 
             simulator₁ P (lookupChoice (proToE P) (proToI P) s)

   simulator₁ : ∀ {i} → {c₀ : Choice} 
                 → (P : Process ∞ c₀) 
                 → Maybe ((ChoiceSet (proToE P)) 
                                      ⊎ (ChoiceSet (proToI P)))
                 → IOConsole i Unit  
   forceIO (simulator₁ P nothing) = 
       do' (putStrLn "please enter correct choice") λ _ →  simulator P
   simulator₁ P (just c₁) = simulator (proPToSubPrP P c₁)



{- start hidden -}
setSTOP : Choice
setSTOP = namedElements ("STOP" ∷ [])

transition₁ : ∀ i → Process i setSTOP
transition₁  i = laba ⟶ delay {i} (labb ⟶ delay {↑ i} (labc ⟶ delay {↑ (↑ i)} STOP))

transition₂ : ∀ i → Process i setSTOP
transition₂  i = laba ⟶ delay {i} (labb ⟶ delay {↑ i} (labc ⟶ delay {↑ (↑ i)} STOP))

myResultType : Choice
myResultType = setSTOP ×' setSTOP

myProcess :  Process ∞ myResultType
myProcess = transition₁ ∞  ||| transition₂ ∞ 

{- end hidden -}

main  : NativeIO Unit 
main  =  translateIOConsole (simulator myProcess)
