module IOInterleav where 

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
open import ooAgda.SizedIO.Console hiding (main)
open import ooAgda.NativeIO
open import externalChoice
open import interleave


setSTOP : Choice
setSTOP = namedElements ("STOP" ∷ [])

transition₁ : ∀ i → Process i setSTOP
transition₁  i = laba ⟶ delay {i} (labb ⟶ delay {↑ i} (labc ⟶ delay {↑ (↑ i)} (STOP {∞} setSTOP)))

transition₂ : ∀ i → Process i setSTOP
transition₂  i = laba ⟶ delay {i} (labb ⟶ delay {↑ i} (labc ⟶ delay {↑ (↑ i)} (STOP {∞} setSTOP)))

transition₄ :  ∀ i → Process i (setSTOP ×' setSTOP)
transition₄ i  = transition₁ i ||| transition₂ i



main  : NativeIO Unit 
main  =  translateIOConsole (myProgram (setSTOP ×' setSTOP) ((transition₄ ∞)))

