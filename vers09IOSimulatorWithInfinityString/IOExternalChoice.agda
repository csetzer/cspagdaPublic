module IOExternalChoice where 

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
process₀  i = laba ⟶  STOP∞ 

process₁ : ∀ i → Process i setSTOP
process₁  i = laba ⟶pp   (labb ⟶pp (labc ⟶ STOP∞  ))

process₂ : ∀ i → Process i setSTOP
process₂  i = labc ⟶ STOP∞ 

process₃ : ∀ i → Process i setSTOP
process₃  i = labb ⟶ STOP∞ 

process₄ : ∀ i → Process i setSTOP
process₄  i =  delay (process₂  i) ⊓ delay (process₃ i)

transition₂ : ∀ i → Process i setSTOP
transition₂  i = laba ⟶ delay {i} (labb ⟶ delay {↑ i} (labc ⟶ delay {↑ (↑ i)} STOP))

process₅ :  ∀ i → Process i ((setSTOP □Res setSTOP) □Res setSTOP)
process₅ i  = (process₁ i □ process₄ i) □ SKIP (ne zero)



main  : NativeIO Unit 
main  =  translateIOConsole (myProgram ((setSTOP □Res setSTOP) □Res setSTOP) (process₅ ∞))

