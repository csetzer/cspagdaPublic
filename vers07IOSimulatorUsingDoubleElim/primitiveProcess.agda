module primitiveProcess where 

open import Size
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import process
open import auxData
open import dataAuxFunction 
open import choiceSetU
open Process∞  
open Process+


STOP₀ : (i : Size) → {A : Set} →  A → Process (↑ i) (A  × String)
STOP₀ i A = terminate (A ,, "STOP") 


Stop₀ :  {i : Size} → {A : Set} →  A → Process (↑ i) (A  × String)
Stop₀ = STOP₀ _

{-
SKIP₀ : (i : Size) → {A : Set} → A →  Process i  (A  × String)
SKIP₀ i x = node (fin 0) efq efq (fin 1) (λ _ → delay i (terminate ((x ,, "SKIP") ))) "SKIP"

Skip₀ :  {i : Size} → {A : Set} → A →  Process i  (A  × String)
Skip₀ = SKIP₀ _
-}


{-Used one-}
STOP : (i : Size) → (c : Choice) → (a : ChoiceSet c) → Process (↑ i) (ChoiceSet c)
STOP i c a = terminate a

Stop :  {i : Size} → {c : Choice} →  ChoiceSet c → Process (↑ i) (ChoiceSet c)
Stop {i} {c} = STOP i c



{-Used one-}
SKIP+ : (i : Size) → (c : Choice) → (a : ChoiceSet c) → Process+ (↑ i) (ChoiceSet c)
E   (SKIP+ i c a)    = fin 0
Lab (SKIP+ i c a) ()
PE (SKIP+ i c a) ()
I   (SKIP+ i c a)    = fin 1
PI  (SKIP+ i c a) x  = delay i (terminate a)
Str (SKIP+ i c a)    = "SKIP"


SKIP : (i : Size) → (c : Choice) → (a : ChoiceSet c) → Process (↑ i) (ChoiceSet c)
SKIP i c a = node (SKIP+ i c a )

Skip : {i : Size} → {c : Choice} → ChoiceSet c → Process (↑ i) (ChoiceSet c)
Skip {i} {c}  = SKIP i c
