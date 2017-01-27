module IOSeqCom where

open import Size 
open import process 
open import choiceSetU
open import preFix   
open import primitiveProcess
open import label
open import sequentialComposition
open import simulator
open import Data.Fin renaming (_+_ to _+,_;_<_ to _<F_)
open import Data.List
open import SizedIO.Console hiding (main)
open import NativeIO



setSTOP : Choice
setSTOP = namedElements ("STOP" ∷ [])

SetSTOP : Set
SetSTOP = ChoiceSet setSTOP

setAB : Choice
setAB = namedElements ("A" ∷ "B" ∷ [])

SetAB : Set
SetAB = ChoiceSet setAB

transition₁ : ∀ i → Process i SetSTOP 
transition₁  i = laba  ⟶ delay i (labb ⟶ delay (↑ i) (labc ⟶ delay (↑ (↑ i)) (STOP ∞ setSTOP (ne zero))))

transition₂ : ∀ i → Process i SetSTOP
transition₂  i = laba ⟶ delay i (labb ⟶ delay (↑ i) (labc ⟶ delay (↑ (↑ i)) (STOP ∞ setSTOP (ne zero))))


transition₃ : ∀ i → Process i SetSTOP
transition₃  i =   transition₁ i ⟫= (λ x → delay i (transition₂ i))



main  :  NativeIO Unit
main  =  translateIOConsole  (myProgram (namedElements ("STOP" ∷ [])) (transition₃ ∞))

