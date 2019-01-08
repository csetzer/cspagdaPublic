module auxData where

open import Data.Bool
open import Data.String.Unsafe renaming (_==_ to _==strb_)
open import Data.String
open import Data.Product hiding ( _×_ )


data _×_ (a b : Set) : Set where
   _,,_  : a → b → a × b


data _∨s_  (a b : Set) : Set where
  inl  : a → a ∨s  b
  inr  : b → a ∨s  b

data subset (A : Set) (f : A → Bool) : Set where
  sub : (a : A) → T (f a) → subset A f


data _==_ {A : Set} (a : A) : A → Set   where
  refl : a == a
