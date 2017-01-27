module testShowFunction where

open import showFunction
open import choiceSetU
open import Data.List
open import Data.Fin
open import Data.String

c : Choice
c = namedElements ("ela"  ∷ "elb" ∷ [])

d : Choice
d = namedElements ("elc"  ∷ "eld" ∷ [])


f : ChoiceSet c → ChoiceSet d
f (ne zero) = ne zero
f (ne (suc zero)) = ne (suc zero)
f (ne (suc (suc ())))

s : String 
s = choiceFunctionToString  (choice2String d) c f 
