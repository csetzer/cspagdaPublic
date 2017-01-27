module IOParallel where




-- _[_]||∞[_]_ : {i : Size} {c₀ c₁ : Choice} → Process∞ i c₀ → (A  B : Label → Bool) → Process∞ i c₁ → Process∞ i (c₀ ×' c₁)



open import Size 
open import process 
open import choiceSetU
open import preFix   
open import primitiveProcess
open import auxData
open import label
open import simulator
open import Data.Fin renaming (_+_ to _+,_;_<_ to _<F_)
open import Data.List
open import SizedIO.Console hiding (main)
open import NativeIO
open import externalChoice
open import interleave
open import internalChoice
open import parallelSimple
open import Data.Bool
open import rec
open import Data.Sum
open import Data.Fin
--open import Data.Nat
open import Data.String
open import SizedIO.Console hiding (main)
open import NativeIO
open import Size
open import rec
open import process
open Process
open Process∞
open Process+
--open import choiceSetU 
--open import preFix
--open import label
--open import primitiveProcess
--open import showLabelP
--open import showFunction
--open import simulator
open import CSPAgdaSyntax



setSTOP : Choice
setSTOP = namedElements ("STOP" ∷ [])

skip : ∀ {i} → Process∞  i setSTOP
skip = delay (SKIP (ne zero))

process₀ : ∀ i → Process i setSTOP
process₀  i = laba ⟶  STOP

process₁ : ∀ i → Process i setSTOP
process₁  i = labb ⟶pp  (laba ⟶  STOP )

process₂ : ∀ i → Process i setSTOP
process₂  i = labc ⟶ STOP 

process₃ : ∀ i → Process i setSTOP
process₃  i = laba ⟶ STOP 

process₄ : ∀ i → Process i setSTOP
process₄  i =  delay (process₂  i) ⊓ delay (process₃ i)

transition₂ : ∀ i → Process i setSTOP
transition₂  i = laba ⟶ labb ⟶ labc ⟶ STOP



c₀ : Choice
c₀ = ⊤'

c₁ : Choice
c₁ = ∅'


P : ∀ {i} →  ChoiceSet c₀ → Process+ (↑ i) (c₀ ⊎' c₁)  
P {i} x = labc ⟶++ (laba ⟶+ (labb ⟶p∞ TERMINATE (inj₁ zero) ))


Q'∞  : ∀ {i} → Process∞ i c₁
Q'∞ {i} =  rec (namedArg "P") P zero

Q'  : ∀ i → Process i c₁
Q' i = forcep Q'∞ 


process₅ :  ∀ i → Process i (c₁ ×' c₁) -- (setSTOP ×' setSTOP) -- ((setSTOP  ⊎' setSTOP)  ⊎' setSTOP)
process₅ i  = Q' i [ (λ labc → true) ]||[ ((λ labc → true)) ] Q' i


main  : NativeIO Unit 
main  =  translateIOConsole (myProgram (c₁ ×' c₁) (process₅ ∞))


-- _[_]||[_]_ : {i : Size} {c₀ c₁ : Choice} → Process∞ i c₀ → (A  B : Label → Bool) → Process∞ i c₁ → Process∞ i (c₀ ×' c₁)


{-
process₅ :  ∀ i → Process i ((setSTOP  ⊎' setSTOP)  ⊎' setSTOP)
process₅ i  = (process₁ i □ process₄ i) □ SKIP (ne zero)

main  : NativeIO Unit 
main  =  translateIOConsole (myProgram ((setSTOP  ⊎' setSTOP)  ⊎' setSTOP) (process₅ ∞))
-}
