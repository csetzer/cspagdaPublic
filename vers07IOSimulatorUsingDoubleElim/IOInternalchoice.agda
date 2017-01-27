module IOInternalchoice where 



open import Size 
open import externalChoice 
open import process 
open Process∞
open import choiceSetU
open import choiceAuxFunction
open import preFix   
open import primitiveProcess
open import auxData
open import label
open import sequentialComposition
open import simulator
open import Size
open import Data.Sum
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat
open import Agda.Builtin.Nat renaming (_<_ to _<N_; _==_ to _==N_)
open import Data.Fin renaming (_+_ to _+,_;_<_ to _<F_)
open import Data.Char renaming (_==_ to _==?_)
open import Data.Maybe
open import Data.Nat 
open import Data.List
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import Data.Nat.Show renaming (show to showℕ)
open import SizedIO.Base  renaming (force to forceIO; delay to delayIO)
open import SizedIO.Console hiding (main)
open import NativeIO
open import Agda.Builtin.Unit
open import Data.List.Base renaming (map to mapL)
open import externalChoice
open import auxData
open import dataAuxFunction
open import choiceSetU
open import internalChoice
open import showFunction 

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
transition₃  i =   transition₁ i ⟫='' (λ x → delay i (transition₂ i))


transition₄ :  ∀ i → Process i ((SetSTOP ⊎ SetSTOP) ⊎ (SetSTOP × SetSTOP))
transition₄ i  = transition₁ i  □ transition₂ i



transition₅ : Process∞ ∞ SetSTOP
transition₅ =  Int setSTOP (λ x → delay ∞ (transition₂ ∞))

f : SetAB → Process∞ ∞ SetSTOP
f (ne zero) = delay ∞ (transition₁ ∞)
f (ne (suc zero)) = delay ∞ (transition₂ ∞)
f (ne (suc (suc ())))

transition₆ : Process∞ ∞ SetSTOP
transition₆ =  Int setAB f



main  : NativeIO Unit 
main  =  translateIOConsole (myProgram setSTOP  (force transition₆ ∞))

