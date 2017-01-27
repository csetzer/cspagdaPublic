module sequentialComposition where


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

funcChoice2ProcessToProcess : ∀ {i} → (c d : Choice) → (ChoiceSet c  → Process i (ChoiceSet d)) → String
funcChoice2ProcessToProcess c d f = unlines (mapL ((λ x → "λ "  ++s (choice2String c x) ++s " → " ++s showProcess d (f x) ++s ")")) (choice2Enumeration0 c))


funcChoice2ProcessToProcess∞ : ∀ {i} → (c d : Choice) → (ChoiceSet c  → ∞Process (↑ i)  (ChoiceSet d)) → String
funcChoice2ProcessToProcess∞ {i} c d f = funcChoice2ProcessToProcess c d (λ x → force (f x ) i )



mutual 
   _⟫='_ : {i : Size} →  {c₀ c₁ : Choice} → ∞Process i (ChoiceSet c₀)  → (ChoiceSet c₀ → ∞Process i (ChoiceSet c₁))
                      → ∞Process i (ChoiceSet c₁)
   force (_⟫='_ {i} {c₀} {c₁} P Q) j  =   _⟫=''_ {j} {c₀} {c₁} (force P j)  Q

   _⟫=''_ : {i : Size} → {c₀ c₁ : Choice} → Process i (ChoiceSet c₀)  → (ChoiceSet c₀ → ∞Process (↑ i) (ChoiceSet c₁))
                       → Process i (ChoiceSet c₁)
   _⟫=''_ {i} {c₀} {c₁} (node E Lab PE I PI Stat)  Q = node E Lab ((λ x → (_⟫='_ {i} {c₀} {c₁} (PE x) Q))) I ((λ x → _⟫='_ {i} {c₀} {c₁} (PI x) Q)) 
                                                       (Stat  ++s ";" ++s funcChoice2ProcessToProcess∞  {i} c₀ c₁ Q)
   _⟫=''_ {i} (terminate x) Q = force (Q x) i
