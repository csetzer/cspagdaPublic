module IOExampleScreenShotForTyDePaper2 where 

open import Size 
open import process 
open import choiceSetU
open import preFix   
open import primitiveProcess
open import auxData
open import label
open import simulator
open import Data.Fin renaming (_+_ to _+,_;_<_ to _<F_)
open import Data.List
open import SizedIO.Console hiding (main)
open import NativeIO
open import externalChoice
open import interleave
open import internalChoice

setSTOP : Choice
setSTOP = namedElements ("STOP" ∷ [])

skip : ∀ {i} → Process∞  i setSTOP
skip = delay (SKIP (ne zero))

process₀ : ∀ i → Process i setSTOP
process₀  i = laba ⟶   STOP 

process₁ : ∀ i → Process i setSTOP
process₁  i = labb ⟶pp  (laba ⟶∞  STOP∞ )

process₂ : ∀ i → Process i setSTOP
process₂  i = labc ⟶ STOP 

process₃ : ∀ i → Process i setSTOP
process₃  i = laba ⟶ STOP 

process₄ : ∀ i → Process i setSTOP
process₄  i =  delay (process₂  i) ⊓ delay (process₃ i)

transition₂ : ∀ i → Process i setSTOP
transition₂  i = laba ⟶ labb ⟶ labc ⟶ STOP

process₅ :  ∀ i → Process i (setSTOP  ⊎' (setSTOP  ⊎' setSTOP))
process₅ i  = process₁ i □ (process₄ i □ SKIP (ne zero))

main  : NativeIO Unit 
main  =  translateIOConsole (myProgram (setSTOP  ⊎' (setSTOP  ⊎' setSTOP)) (process₅ ∞))

