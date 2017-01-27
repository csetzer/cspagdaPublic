module IOInternalchoice where 

open import process 
open Process∞
open import preFix   
open import primitiveProcess
open import label
open import sequentialComposition
open import simulator
open import Size
open import Data.Fin renaming (_+_ to _+,_;_<_ to _<F_)
open import SizedIO.Console hiding (main)
open import NativeIO
open import Data.List.Base renaming (map to mapL)
open import externalChoice
open import choiceSetU
open import internalChoice


setSTOP : Choice
setSTOP = namedElements ("STOP" ∷ [])

SetSTOP : Set
SetSTOP = ChoiceSet setSTOP

setAB : Choice
setAB = namedElements ("A" ∷ "B" ∷ [])

SetAB : Set
SetAB = ChoiceSet setAB

transition₁ : ∀ i → Process i setSTOP 
transition₁  i = laba  ⟶ delay {i} (labb ⟶ delay {↑ i} (labc ⟶ delay {↑ (↑ i)} STOP))

transition₂ : ∀ i → Process i setSTOP
transition₂  i = laba ⟶ delay {i} (labb ⟶ delay {↑ i} (labc ⟶ delay {↑ (↑ i)} STOP))

transition₃ : ∀ i → Process i setSTOP
transition₃  i =   transition₁ i ⟫= (λ x → delay {i} (transition₂ i))

transition₄ :  ∀ i → Process i (setSTOP ⊎' setSTOP)
transition₄ i  = transition₁ i  □ transition₂ i

transition₅ : Process∞ ∞ setSTOP
transition₅ =  IntChoice∞ ∞ setSTOP (λ x → delay {∞} (transition₂ ∞))

f : SetAB → Process∞ ∞ setSTOP
f (ne zero) = delay {∞} (transition₁ ∞)
f (ne (suc zero)) = delay {∞} (transition₂ ∞)
f (ne (suc (suc ())))

transition₆ : Process∞ ∞ setSTOP
transition₆ =  IntChoice∞ ∞ setAB f

main  : NativeIO Unit 
main  =  translateIOConsole (myProgram setSTOP  (forcep transition₆ {∞}))

