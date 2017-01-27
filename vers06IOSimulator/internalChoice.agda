module internalChoice where 


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
open import choiceSetU
open import process
open ∞Process
open import showFunction
open import auxData
open import dataAuxFunction

funcChoice2ProcessToProcess₁ : ∀ {i} → {c₀ : Choice} → (c : Choice) → (ChoiceSet c  → Process i (ChoiceSet c₀)) → String
funcChoice2ProcessToProcess₁ {i} {c₀} c f = unlines (mapL ((λ x → "(λ "  ++s (choice2String c x) ++s " → " ++s showProcess c₀ (f x) ++s ")")) (choice2Enumeration0 c))


funcChoice2ProcessToProcess₁∞ : ∀ {i}  → {c₀ : Choice} → (c : Choice) → (ChoiceSet c  → ∞Process (↑ i)  (ChoiceSet c₀)) → String
funcChoice2ProcessToProcess₁∞ {i} c f = funcChoice2ProcessToProcess₁ c (λ x → force (f x ) i )


IntChoice : (i : Size) → {c₀ : Choice} → (c : Choice) 
          → (PI : ChoiceSet c → ∞Process i (ChoiceSet c₀)) 
          → ∞Process i (ChoiceSet c₀) 
force (IntChoice i {c₀} c PI) j = node (fin 0) efq efq c PI (" \t ∪ \t " ++s funcChoice2ProcessToProcess₁∞ c PI) 


Int : {i : Size} → {c₀ : Choice} → (c : Choice) 
       → (PI : ChoiceSet c → ∞Process i (ChoiceSet c₀)) 
       → ∞Process i (ChoiceSet c₀) 
Int =  IntChoice _


{-
test : Set
test = {!!}
-}
