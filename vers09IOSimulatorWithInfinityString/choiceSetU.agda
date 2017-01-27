module choiceSetU where

open import auxData
open import dataAuxFunction
open import Data.Bool
open import Data.Nat
open import Data.Fin renaming (_+_ to _+,_;_<_ to _<F_)
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List.Base renaming (map to mapL)
open import Data.Maybe
open import Data.Bool.Base
open import Agda.Builtin.Unit
open import Data.Product hiding ( _×_ )
open import Data.Sum

data NamedElements (s : List String) : Set where
  ne : Fin (length s) → NamedElements s

mutual
 data Choice : Set where 
  fin   : ℕ → Choice
  _⊎'_    : Choice → Choice → Choice
  _×'_    : Choice → Choice → Choice
  subset' : (E : Choice) →  (ChoiceSet E → Bool) → Choice
  Σ'      : (E : Choice) →  (ChoiceSet E → Choice) → Choice
  namedElements : List String → Choice

 ChoiceSet : Choice → Set 
 ChoiceSet (fin n) = Fin n
 ChoiceSet (s ⊎' t) = ChoiceSet s ⊎ ChoiceSet t
 ChoiceSet (E ×' F) = ChoiceSet E × ChoiceSet F 
 ChoiceSet (Σ' A B) = Σ[ x ∈ ChoiceSet A ] ChoiceSet (B x) 
 ChoiceSet (namedElements s) = NamedElements s
 ChoiceSet (subset' E f) = subset (ChoiceSet E) f

 
∅' : Choice
∅' = fin 0

⊤' : Choice
⊤' = fin 1


nth : {A : Set} → (l : List A) → Fin (length l) → A
nth [] ()
nth (a ∷ l) zero = a
nth (a ∷ l) (suc n) = nth l n

choice2Str : {c : Choice} → ChoiceSet c  → String
choice2Str {fin n} m = showℕ (toℕ m)
choice2Str {c₀ ⊎' c₁} (inj₁ a) = "(inl " ++s (choice2Str {c₀} a) ++s ")"
choice2Str {c₀ ⊎' c₁} (inj₂ a) = "(inr " ++s (choice2Str {c₁} a) ++s ")"
choice2Str {c₀ ×' c₁} (x ,, x₁) = "(" ++s (choice2Str {c₀} x) ++s ",," ++s (choice2Str {c₁} x₁) ++s ")"
choice2Str {namedElements s} (ne i) = nth s i
choice2Str {Σ' c₀ c₁} (x₁ , x₂₁) = (choice2Str {c₀} x₁) ++s "," ++s (choice2Str {c₁ x₁} x₂₁)
choice2Str {subset' E f} (sub a x) = choice2Str {E} a

choice2Stri : (c : Choice) → ChoiceSet c  → String
choice2Stri c a = choice2Str {c} a  

boolToMaybeTrue : (b : Bool) → Maybe (T b)
boolToMaybeTrue false = nothing
boolToMaybeTrue true = just tt

set2MaybeSubset0  : (A : Set) → (f : A → Bool) → (a : A) → Maybe (T (f a))  → Maybe (subset A f)
set2MaybeSubset0 A f a (just p) = just (sub a p)
set2MaybeSubset0 A f a nothing = nothing

set2MaybeSubset  : (A : Set) → (f : A → Bool) → A → Maybe (subset A f)
set2MaybeSubset  A f a = set2MaybeSubset0 A f a (boolToMaybeTrue (f a))


choice2Enum : (c : Choice) → List (ChoiceSet c)   
choice2Enum (fin n) = fin2Option0 n                                
choice2Enum (c₀ ⊎' c₁) = mapL (λ a → inj₁ a) (choice2Enum c₀) ++ 
                                  mapL (λ a → inj₂ a) (choice2Enum c₁) 
choice2Enum (c₀ ×' c₁) = concat (mapL  (λ a → (mapL (λ b → (a ,, b)) (choice2Enum c₁) ))  (choice2Enum c₀))
--                                 let 
--                                     c = mapL  (λ a → (mapL (λ b → (a , b)) (choice2Enum c₁) ))  (choice2Enum c₀)
--                                 in concat c -- {!(choice2Enum c₀) , (choice2Enum c₁)!}                    
choice2Enum (namedElements s) = mapL (λ i → ne i) (fin2Option0 (length s))                                -- unit ∷ []
choice2Enum (Σ' c₀ c₁) = concat (mapL  (λ a → (mapL (λ b → (a , b)) (choice2Enum (c₁ a)) ))  (choice2Enum c₀))
choice2Enum (subset' E f) = gfilter (set2MaybeSubset (ChoiceSet E) f) (choice2Enum E)

choiceIsEmpty : Choice → Bool
choiceIsEmpty c = null (choice2Enum c)



--let
--                                    f : (a : ChoiceSet c₀) → ChoiceSet (c₁ a) → ChoiceSet (Σ' c₀ c₁)
--                                    f a b = (a , b)

--                                    l : (a : ChoiceSet c₀) → List (ChoiceSet (Σ' c₀ c₁))
--                                    l a = mapL (λ b → (a , b)) (choice2Enum (c₁ a))
--                               in
--                                  c = mapL  (λ a → (mapL (λ b → (a , b)) (choice2Enum (c₁ a)) ))  (choice2Enum c₀)
--                                 {! !}
--choice2Enum (subset' E f) = {!!}

 
--   mapL  (λ a → (mapL (λ b → (a , b)) (choice2Enum c₁) ))  (choice2Enum c₀)
--                 --------------------------------------------------
--                 if (choice2Enum c₁) = (b_0, b_1)
--                   it creates  [ (a,b_0), (a,b_1)]
--                 if (choice2Enum c₀) = (a_0, a_1)
--                 you get [ [ (a_0,b_0), (a_0,b_1)] , [ (a_1,b_0), (a_1,b_1)] ]
--
--       now take function   List (List A) -> List A


