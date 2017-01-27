module testShowFunction where

open import Data.List
open import Data.Fin
open import Data.String
open import ooAgda.SizedIO.Console hiding (main)
open import ooAgda.NativeIO
open import Size
open import showFunction
open import choiceSetU
open import testExampleProcesses
open import primitiveProcess
open import process
open import externalChoice
open import simulator

c : Choice
c = namedElements ("ela"  ∷ "elb" ∷ [])

d : Choice
d = namedElements ("elc"  ∷ "eld" ∷ [])


f : ChoiceSet c → ChoiceSet d
f (ne zero) = ne zero
f (ne (suc zero)) = ne (suc zero)
f (ne (suc (suc ())))

-- s : String 
-- s = choiceFunctionToString  (choice2Str ?) c f 


s : String
s = showTicks transition₄

s2 : String
s2 = showTicks (SKIP {∞} {fin 1} zero)

skip : Process ∞ (fin 1)
skip = SKIP {∞} {fin 1} zero

P : Process ∞ (fin 1 ⊎' setSTOP) 
P = skip □ transition₁

s3 : String
s3 = showTicks P

s4 : String
s4 = showLabels₁ P

main  : NativeIO Unit 
main  =  translateIOConsole (myProgrami P)



