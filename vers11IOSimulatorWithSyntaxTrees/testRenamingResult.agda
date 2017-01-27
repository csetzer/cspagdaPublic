module testRenamingResult where

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
open import renamingResult
open import IOInternalchoice hiding (f )

f : SetSTOP → ChoiceSet (fin 3)
f (ne zero) = suc zero
f (ne (suc ())) 

g : Fin 3 → Fin 4
g zero = suc zero
g (suc zero) = zero
g (suc (suc zero)) = zero
g (suc (suc (suc ())))

Q : Process ∞ (fin 3)
Q = fmap f (transition₂ ∞)

s : String
s = Str Q

Q' : Process ∞ (fin 4)
Q' = fmap g Q


s' : String
s' = Str Q'
