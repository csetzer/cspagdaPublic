module IOExtchoice where 


open import Size 
open import externalChoice 
open import process 
open import choiceSetU
open import preFix   
open import primitiveProcess
open import auxData
open import label
open import sequentialComposition
open import simulator
open import Data.Sum
open import Data.Fin renaming (_+_ to _+,_;_<_ to _<F_)
open import Data.List
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import ooAgda.SizedIO.Console hiding (main)
open import ooAgda.NativeIO








setSTOP : Choice
setSTOP = namedElements ("STOP" ∷ [])

SetSTOP : Set
SetSTOP = ChoiceSet setSTOP


transition₁ : ∀ i → Process i setSTOP
transition₁  i = laba ⟶ delay {i} (labb ⟶ delay {↑ i} (labc ⟶ delay {↑ (↑ i)} (STOP {∞} setSTOP)))

transition₂ : ∀ i → Process i setSTOP 
transition₂  i = laba ⟶ delay {i} (labb ⟶ delay {↑ i} (labc ⟶ delay {↑ (↑ i)} (STOP {∞} setSTOP)))


transition₃ : ∀ i → Process i setSTOP
transition₃  i =   transition₁ i ⟫= (λ x → delay {i} (transition₂ i))


transition₄ :  ∀ i → Process i (setSTOP ⊎' setSTOP)
transition₄ i  = transition₁ i  □ transition₂ i



main  : NativeIO Unit 
main  =  translateIOConsole (myProgram (setSTOP ⊎' setSTOP)  ((transition₄ ∞)))

