module testRenamingOperator where

open import testExampleProcesses
open import renamingOperator
open import Size 
open import label
open import process
open import choiceSetU
open import Data.String
open import showFunction
open import showLabelP
open import Data.Sum
open import auxData
open import externalChoice

f : Label → Label
f laba = labb
f labb = labc
f labc = laba

P : Process ∞ setSTOP
P = transition₁ ∞ 

pToStr : String
pToStr = Str P

pToLabels : String
pToLabels = showLabels₁ P

Q : Process ∞ setSTOP
Q = Rename f P

qToStr : String
qToStr = Str  Q

qToLabels : String
qToLabels = showLabels₁ Q


P2Result : Choice
P2Result = setSTOP ⊎' setSTOP

P2  :  Process ∞ P2Result
P2 = transition₄ ∞ 

p2ToStr : String
p2ToStr = Str  P2

p2ToLabels : String
p2ToLabels = showLabels₁ P2

Q2 : Process ∞ P2Result
Q2 = Rename f P2

q2ToStr : String
q2ToStr = Str  Q2



q2ToLabels : String
q2ToLabels = showLabels₁ Q2
