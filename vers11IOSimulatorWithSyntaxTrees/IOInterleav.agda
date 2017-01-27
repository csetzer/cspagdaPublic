module IOInterleav where 


open import Size 
open import externalChoice 
open import process 
open import choiceSetU
open import preFix   
open import primitiveProcess
open import auxData
open import label
open import simulator
open import Data.List
open import SizedIO.Console hiding (main)
open import NativeIO
open import interleave


setSTOP : Choice
setSTOP = namedElements ("STOP" ∷ [])

SetSTOP : Set
SetSTOP = ChoiceSet setSTOP

transition₁ : ∀ i → Process i setSTOP
transition₁  i = laba ⟶ delay {i} (labb ⟶ delay {↑ i} (labc ⟶ delay {↑ (↑ i)} STOP))

transition₂ : ∀ i → Process i setSTOP 
transition₂  i = labc ⟶ delay {i} (labb ⟶ delay {↑ i} (laba ⟶ delay {↑ (↑ i)} STOP))

transition₄ :  ∀ i → Process i (setSTOP ×' setSTOP)
transition₄ i  = transition₁ i ||| transition₂ i 

main  : NativeIO Unit 
main  =  translateIOConsole (myProgram (setSTOP ×' setSTOP) ((transition₄ ∞)))

