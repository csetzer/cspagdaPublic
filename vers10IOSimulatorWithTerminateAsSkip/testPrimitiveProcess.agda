module testPrimitiveProcess where 

open import Size
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import Data.List
open import process
open import auxData
open import dataAuxFunction 
open import choiceSetU
open import primitiveProcess
open import sequentialComposition
open import Data.Fin
open Process∞  
open Process+
open import simulator
open import SizedIO.Console hiding (main)
open import NativeIO

myskip : Process ∞ (fin 1)
myskip = SKIP zero


skip>>terminate : Process ∞ (fin 1)
skip>>terminate = myskip ⟫= (delay ∘ terminate) -- (λ a → delay (terminate a))

main  : NativeIO Unit 
main  =  translateIOConsole (myProgram (fin 1) skip>>terminate)

