module exampleFinFun where

open import Data.Fin renaming (toℕ to toℕ₁)
open import Data.Nat


toℕ : ∀ {n} → Fin n → ℕ
toℕ  zero     =  0
toℕ  (suc n)  =  suc (toℕ n)
