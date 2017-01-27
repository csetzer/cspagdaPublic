module choiceAuxFunction where

open import auxData
open import choiceSetU 
open import Data.Bool
open import Data.Maybe
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import Data.List.Base renaming (map to mapL)
open import Data.Sum
open import Data.Product hiding ( _×_ )

extChoiceElToName : String → String
extChoiceElToName s = "ext(" ++s s ++s ")"

intChoiceElToName : String → String
intChoiceElToName s = "int(" ++s s ++s ")"



choice2EnumStr : (c : Choice) → List (String × ChoiceSet c)   
choice2EnumStr c  =  mapL (λ a → (choice2Str a ,, a)) (choice2Enum c)


mutual 
  lookupInEnum : {A : Set} → List (String × A) → String → Maybe A
  lookupInEnum [] str = nothing
  lookupInEnum ((str' ,, a) ∷ l) str = lookupInEnumAux a l str (str' ==strb str)

  lookupInEnumAux : {A : Set} → A  → List (String × A) → String → Bool → Maybe A
  lookupInEnumAux a l s false = lookupInEnum l s
  lookupInEnumAux a l s true = just a



combineEnumerations : {E I : Choice} →  List (String × ChoiceSet E) → List (String × ChoiceSet I) → List (String × (ChoiceSet E ⊎ ChoiceSet I))
combineEnumerations {E} {I}  L L' =  (mapL (λ {( s ,, c) → (extChoiceElToName s ,, inj₁ c)}) L) ++ (mapL (λ {( s ,, c) → (intChoiceElToName s ,, inj₂ c)}) L')

lookupChoice : (E I : Choice) → String → Maybe (ChoiceSet E ⊎ ChoiceSet I)
lookupChoice E I s = lookupInEnum  (combineEnumerations (choice2EnumStr E) (choice2EnumStr I)) s

