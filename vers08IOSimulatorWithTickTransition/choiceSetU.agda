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
  _+''_    : Choice → Choice → Choice
  _×'_    : Choice → Choice → Choice
  subset' : (E : Choice) →  (ChoiceSet E → Bool) → Choice
  Σ'      : (E : Choice) →  (ChoiceSet E → Choice) → Choice
  namedElements : List String → Choice

 ChoiceSet : Choice → Set 
 ChoiceSet (fin n) = Fin n
 ChoiceSet (s +'' t) = ChoiceSet s ⊎ ChoiceSet t
 ChoiceSet (E ×' F) = ChoiceSet E × ChoiceSet F 
 ChoiceSet (Σ' A B) = Σ[ x ∈ ChoiceSet A ] ChoiceSet (B x) 
 ChoiceSet (namedElements s) = NamedElements s
 ChoiceSet (subset' E f) = subset (ChoiceSet E) f

 
empty : Choice
empty = fin 0

unitc : Choice
unitc = fin 1


nth : {A : Set} → (l : List A) → Fin (length l) → A
nth [] ()
nth (a ∷ l) zero = a
nth (a ∷ l) (suc n) = nth l n

choice2String : (c : Choice) → ChoiceSet c  → String
choice2String (fin n) m = showℕ (toℕ m)
choice2String (c₀ +'' c₁) (inj₁ a) = "inl(" ++s (choice2String c₀ a) ++s ")"
choice2String (c₀ +'' c₁) (inj₂ a) = "inr(" ++s (choice2String c₁ a) ++s ")"
choice2String (c₀ ×' c₁) (x ,, x₁) = "(" ++s (choice2String c₀ x) ++s ",," ++s (choice2String c₁ x₁) ++s ")"
choice2String (namedElements s) (ne i) = nth s i
choice2String (Σ' c₀ c₁) (x₁ , x₂₁) = (choice2String c₀ x₁) ++s "," ++s (choice2String (c₁ x₁) x₂₁)
choice2String (subset' E f) (sub a x) = choice2String E a

boolToMaybeTrue : (b : Bool) → Maybe (T b)
boolToMaybeTrue false = nothing
boolToMaybeTrue true = just tt

set2MaybeSubset0  : (A : Set) → (f : A → Bool) → (a : A) → Maybe (T (f a))  → Maybe (subset A f)
set2MaybeSubset0 A f a (just p) = just (sub a p)
set2MaybeSubset0 A f a nothing = nothing

set2MaybeSubset  : (A : Set) → (f : A → Bool) → A → Maybe (subset A f)
set2MaybeSubset  A f a = set2MaybeSubset0 A f a (boolToMaybeTrue (f a))


choice2Enumeration0 : (c : Choice) → List (ChoiceSet c)   
choice2Enumeration0 (fin n) = fin2Option0 n                                
choice2Enumeration0 (c₀ +'' c₁) = mapL (λ a → inj₁ a) (choice2Enumeration0 c₀) ++ 
                                  mapL (λ a → inj₂ a) (choice2Enumeration0 c₁) 
choice2Enumeration0 (c₀ ×' c₁) = concat (mapL  (λ a → (mapL (λ b → (a ,, b)) (choice2Enumeration0 c₁) ))  (choice2Enumeration0 c₀))
--                                 let 
--                                     c = mapL  (λ a → (mapL (λ b → (a , b)) (choice2Enumeration0 c₁) ))  (choice2Enumeration0 c₀)
--                                 in concat c -- {!(choice2Enumeration0 c₀) , (choice2Enumeration0 c₁)!}                    
choice2Enumeration0 (namedElements s) = mapL (λ i → ne i) (fin2Option0 (length s))                                -- unit ∷ []
choice2Enumeration0 (Σ' c₀ c₁) = concat (mapL  (λ a → (mapL (λ b → (a , b)) (choice2Enumeration0 (c₁ a)) ))  (choice2Enumeration0 c₀))
choice2Enumeration0 (subset' E f) = gfilter (set2MaybeSubset (ChoiceSet E) f) (choice2Enumeration0 E)

choiceIsEmpty : Choice → Bool
choiceIsEmpty c = null (choice2Enumeration0 c)



--let
--                                    f : (a : ChoiceSet c₀) → ChoiceSet (c₁ a) → ChoiceSet (Σ' c₀ c₁)
--                                    f a b = (a , b)

--                                    l : (a : ChoiceSet c₀) → List (ChoiceSet (Σ' c₀ c₁))
--                                    l a = mapL (λ b → (a , b)) (choice2Enumeration0 (c₁ a))
--                               in
--                                  c = mapL  (λ a → (mapL (λ b → (a , b)) (choice2Enumeration0 (c₁ a)) ))  (choice2Enumeration0 c₀)
--                                 {! !}
--choice2Enumeration0 (subset' E f) = {!!}

 
--   mapL  (λ a → (mapL (λ b → (a , b)) (choice2Enumeration0 c₁) ))  (choice2Enumeration0 c₀)
--                 --------------------------------------------------
--                 if (choice2Enumeration0 c₁) = (b_0, b_1)
--                   it creates  [ (a,b_0), (a,b_1)]
--                 if (choice2Enumeration0 c₀) = (a_0, a_1)
--                 you get [ [ (a_0,b_0), (a_0,b_1)] , [ (a_1,b_0), (a_1,b_1)] ]
--
--       now take function   List (List A) -> List A



