module IOSeqCom where

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

transition₁ : ∀ i → Process i (ChoiceSet (namedElement "STOP"))
transition₁  i = laba ⟶ delay i (labb ⟶ delay (↑ i) (labc ⟶ delay (↑ (↑ i)) (STOP ∞ (namedElement "STOP") unit)))

transition₂ : ∀ i → Process i (ChoiceSet (namedElement "STOP"))
transition₂  i = laba ⟶ delay i (labb ⟶ delay (↑ i) (labc ⟶ delay (↑ (↑ i)) (STOP ∞ (namedElement "STOP") unit)))



transition₃ : ∀ i → Process i (ChoiceSet (namedElement "STOP"))
transition₃  i =   transition₁ i ⟫='' (λ x → delay i (transition₂ i))



main  :  NativeIO Unit
main  =  translateIOConsole  (myProgram (namedElement "STOP") (transition₃ ∞))


{-
transition₄ :  ∀ i → Process i ((ChoiceSet (namedElement "STOP") +'
                                  ChoiceSet (namedElement "STOP"))
                                 +'
                                 (ChoiceSet (namedElement "STOP") × ChoiceSet (namedElement "STOP")))
transition₄ i  = transition₁ i  □' transition₂ i



main₀  :  NativeIO Unit
main₀  =  translateIOConsole  (myProgram (namedElement "STOP") (transition₂ ∞))


main₁₀  :  NativeIO Unit
main₁₀  =  translateIOConsole  (myProgram (namedElement "STOP") (transition₃ ∞))


main₉  : NativeIO Unit 
main₉  =  translateIOConsole (myProgram ((namedElement "STOP" +'' namedElement "STOP") +''
                                         (namedElement "STOP" ×' namedElement "STOP"))  ((transition₄ ∞)))

-}
