{-# OPTIONS --copatterns #-}

module process where

open import Size
postulate Label    : Set  

--------------------- We introduce general Basic Types and Functions -------------
data Bool : Set where
  tt ff : Bool

data ⊤ : Set where 
 triv : ⊤ 

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥ 

data ∅ : Set where


efq : {A : Set} →  ∅ →  A  
efq ()

data True : Bool → Set  where 
  triv : True tt

¬b : Bool → Bool 
¬b tt = ff
¬b ff = tt

data _×_ (A B : Set) : Set where
  _,_  : A → B → A × B       -- \times = ×

data _+_ (A B : Set) : Set where
  inl  : A → A + B 
  inr  : B → A + B

data _∨_  (A B : Set) : Set where
  inl  : A → A ∨  B 
  inr  : B → A ∨  B

data List (A : Set ) : Set where
  [] : List A 
  _::_ : A → List A → List A  

infixl 10 _::_

data subset (A : Set) (f : A → Bool) : Set where
  sub : (a : A) → True (f a) → subset A f

data Σ (A : Set) (B : A → Set) : Set where
  _,,_  : (a : A) → B a → Σ A B      


Σ-syntax : (A : Set) → (A → Set) → Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

data _==_ {A : Set} (a : A) : A → Set   where 
  refl : a == a

transfer : {A : Set} → (C : A → Set) → (a a' : A) → a == a' → C a → C a'
transfer C a .a refl c = c

projSubset : {A : Set} → {f : A → Bool}  → subset A f → A
projSubset (sub a x) = a


_∘_ : {A B C : Set} →  (B →  C) →  (A →  B) →  A →  C  
(f ∘ g) a = f ( g a )


π₀ : {A B : Set} →  A × B →  A    
π₀ ( a , b) = a

π₁ : {A B : Set} →  A × B →  B    
π₁ ( a , b) = b

mutual
  data Choice : Set where
    ⊤'      : Choice  
    ∅'      : Choice
    Bool'   : Choice
    _×'_    : Choice → Choice → Choice
    _+'_    : Choice → Choice → Choice
    subset' : (E : Choice) →  (ChoiceSet E → Bool) → Choice
    Σ'      : (E : Choice) →  (ChoiceSet E → Choice) → Choice

  ChoiceSet : Choice → Set 
  ChoiceSet ⊤' = ⊤ 
  ChoiceSet ∅' = ∅
  ChoiceSet Bool' = Bool
  ChoiceSet (E ×' F) = ChoiceSet E × ChoiceSet F
  ChoiceSet (E +' F) = ChoiceSet E + ChoiceSet F
  ChoiceSet (subset' E f) = subset (ChoiceSet E) f
  ChoiceSet (Σ' A B) = Σ[ x ∈ ChoiceSet A ] ChoiceSet (B x) 


