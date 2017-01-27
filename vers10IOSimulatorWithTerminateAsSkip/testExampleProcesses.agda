module testExampleProcesses where

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
open import SizedIO.Console hiding (main)
open import NativeIO

setSTOP : Choice
setSTOP = namedElements ("STOP" ∷ [])

SetSTOP : Set
SetSTOP = ChoiceSet setSTOP


transition₁ : ∀ {i} → Process i setSTOP
transition₁  = laba ⟶ delay (labb ⟶ delay (labc ⟶ delay STOP ))

transition₂ : ∀ {i} → Process i setSTOP 
transition₂  = labb ⟶ delay (labc ⟶ delay (laba ⟶ delay STOP))


transition₃ : ∀ {i} → Process i setSTOP
transition₃  =   transition₁ ⟫= (λ x → delay transition₂)


transition₄ :  ∀ {i} → Process i (setSTOP ⊎' setSTOP)
transition₄  = transition₁  □ transition₂ 


