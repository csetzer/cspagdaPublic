module auxData where

open import Data.Bool
open import Data.String renaming  (_==_ to _==strb_)
open import Data.Product hiding ( _×_ )

-- data True : Bool → Set  where 
--  triv : True true


data _×_ (a b : Set) : Set where
   _,,_  : a → b → a × b  


-- data _+'_ (a b : Set) : Set where
--  inl  : a → a +' b 
--  inr  : b → a +' b


data _∨s_  (a b : Set) : Set where
  inl  : a → a ∨s  b 
  inr  : b → a ∨s  b


data subset (A : Set) (f : A → Bool) : Set where
  sub : (a : A) → T (f a) → subset A f


-- data Σ (A : Set) (B : A → Set) : Set where
--   _,,_  : (a : A) → B a → Σ A B      


-- Σ-syntax : (A : Set) → (A → Set) → Set
-- Σ-syntax = Σ


-- syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B


data _==_ {A : Set} (a : A) : A → Set   where 
  refl : a == a



-- data NamedSet (s : String) : Set where
--   unit : NamedSet s
