module testRec where

open import Data.Sum
open import Data.Fin
open import Data.Nat
open import Data.String
open import SizedIO.Console hiding (main)
open import NativeIO
open import Size
open import rec
open import process
open Process∞
open Process+
open import choiceSetU 
open import preFix
open import label
open import primitiveProcess
open import showLabelP
open import showFunction
open import simulator


c₀ : Choice
c₀ = ⊤'

c₁ : Choice
c₁ = ∅'


P : ∀ {i} →  ChoiceSet c₀ → Process+ (↑ i) (c₀ ⊎' c₁)  
P {i} x = labc ⟶++ (laba ⟶+ (labb ⟶p∞ TERMINATE (inj₁ zero) ))

TERMINATEToStr : String
TERMINATEToStr = Str∞ (TERMINATE∞ {∞} {(c₀ ⊎' c₁)}  (inj₁ zero))


p+ToStr : String
p+ToStr = Str+  (P zero)

Q∞  : ∀ {i} → Process∞ i c₁ 
Q∞ {i} = recAutoStr P zero

Q  : ∀ {i} → Process i c₁ 
Q  = forcep Q∞ 

q∞ToStr : String
q∞ToStr = Str∞   Q∞ 



qToStr : String
qToStr = Str  Q

qToLabels : String
qToLabels = showLabels₁ Q


Q'∞  : ∀ {i} → Process∞ i c₁ 
Q'∞ {i} = rec "c \t→\t P" P zero

Q'  : ∀ {i} → Process i c₁ 
Q' = forcep Q'∞ 

q'∞ToStr : String
q'∞ToStr = Str∞   Q'∞ 



q'ToStr : String
q'ToStr = Str  Q'

q'ToLabels : String
q'ToLabels = showLabels₁ Q'

Q'' : Process  ∞ c₁
Q'' = processToSubprocess (Q' {∞})  (inj₁ zero)


q''ToStr : String
q''ToStr = Str   Q'' 


q''ToLabels : String
q''ToLabels = showLabels₁ Q''


Q∞''' : Process∞ ∞ c₁
Q∞''' = processToSubprocess0 Q''   (inj₁ zero) 

Q''' : Process  ∞ c₁
Q''' = processToSubprocess Q''   (inj₁ zero)  

q∞'''ToStr : String
q∞'''ToStr = Str∞ Q∞''' 


q'''ToStr : String
q'''ToStr = Str   Q''' 


q'''ToLabels : String
q'''ToLabels = showLabels₁ Q'''


main  : NativeIO Unit 
main  =  translateIOConsole (myProgrami (Q' {∞}) ) -- (Q∞  {∞} ))
