module IOInterleave where 



open import Size 
open import externalChoice 
open import process 
open ∞Process
open import choiceSetU
open import choiceAuxFunction
open import priFix   
open import primtiveProcess
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
open import interleave
open import showFunction


transition₁ : ∀ i → Process i (ChoiceSet (namedElement "STOP"))
transition₁  i = laba ⟶ delay i (labb ⟶ delay (↑ i) (labc ⟶ delay (↑ (↑ i)) (STOP ∞ (namedElement "STOP") unit)))

transition₂ : ∀ i → Process i (ChoiceSet (namedElement "STOP"))
transition₂  i = laba ⟶ delay i (labb ⟶ delay (↑ i) (labc ⟶ delay (↑ (↑ i)) (STOP ∞ (namedElement "STOP") unit)))

transition₄ :  ∀ i → Process i (ChoiceSet (namedElement "STOP") × ChoiceSet (namedElement "STOP"))
transition₄ i  = transition₁ i ||| transition₂ i



main  : NativeIO Unit 
main  =  translateIOConsole (myProgram (namedElement "STOP" ×' namedElement "STOP")  ((transition₄ ∞)))


-- p = transition₄ ∞

-- q : Set
-- q = {!showLabels₁ p!}

-- choice2Enumeration (processToE p) 
--("inl(0)" , inl zero) ∷ ("inr(0)" , inr zero) ∷ []

-- processToE p
-- fin 1 +'' fin 1

-- showLabels₁ p
-- returns "inl(0):a"

-- processToE p   evaluates to fin 1 +'' fin 1
