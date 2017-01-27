module choiceSetU where

open import auxData
open import dataAuxFunction
open import Data.Nat
open import Data.Fin       renaming (_+_  to _+,_ ; _<_     to _<F_ )
open import Data.String    renaming (_==_ to _==strb_; _++_ to _++s_)
open import Data.List.Base renaming (map to mapL)
open import Data.Bool.Base
open import Data.Product   hiding ( _×_ )
open import Data.Sum

infixl 3 _⊎'_
infixl 4 _×'_

data NamedElements (s : List String) : Set where
  ne : Fin (length s) → NamedElements s


mutual
 data Choice : Set where 
  fin           : ℕ → Choice
  _⊎'_          : Choice → Choice → Choice
  _×'_          : Choice → Choice → Choice
  namedElements : List String → Choice
  subset'       : (E : Choice) → (ChoiceSet E →  Bool)  →  Choice
  Σ'            : (E : Choice) → (ChoiceSet E → Choice) →  Choice

 ChoiceSet : Choice → Set 
 ChoiceSet  (fin n)           =  Fin n
 ChoiceSet  (s ⊎' t)          =  ChoiceSet  s  ⊎  ChoiceSet  t
 ChoiceSet  (E ×' F)          =  ChoiceSet  E  ×  ChoiceSet  F 
 ChoiceSet  (namedElements s) = NamedElements s
 ChoiceSet  (subset' E f)     = subset (ChoiceSet E) f
 ChoiceSet  (Σ' A B)          =  Σ[ x ∈ ChoiceSet A ] ChoiceSet (B x) 

∅' : Choice
∅' = fin 0

⊤' : Choice
⊤' = fin 1

bool : Choice
bool = fin 2
