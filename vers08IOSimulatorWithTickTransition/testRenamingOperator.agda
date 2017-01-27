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


f : Label → Label
f laba = labb
f labb = labc
f labc = laba

P : Process ∞ (ChoiceSet setSTOP)
P = transition₁ ∞ 

pToStr : String
pToStr = showProcess0  P

pToLabels : String
pToLabels = showLabels₁ P

Q : Process ∞ (ChoiceSet setSTOP)
Q = Rename ∞ f P

qToStr : String
qToStr = showProcess0  Q

qToLabels : String
qToLabels = showLabels₁ Q


P2Result : Set
P2Result = ((ChoiceSet setSTOP ⊎ ChoiceSet setSTOP)  ⊎ (ChoiceSet setSTOP × ChoiceSet setSTOP))

P2  :  Process ∞ P2Result
P2 = transition₄ ∞ 

p2ToStr : String
p2ToStr = showProcess0  P2

p2ToLabels : String
p2ToLabels = showLabels₁ P2

Q2 : Process ∞ P2Result
Q2 = Rename ∞ f P2

q2ToStr : String
q2ToStr = showProcess0  Q2



q2ToLabels : String
q2ToLabels = showLabels₁ Q2
