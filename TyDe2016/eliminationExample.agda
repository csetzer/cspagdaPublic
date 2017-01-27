module eliminationExample where 

open import Size
open import Data.Nat

postulate Label    : Set  



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
  _,_  : A → B → A × B    

data _⊎_ (A B : Set) : Set where
  inl  : A → A ⊎ B 
  inr  : B → A ⊎ B

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
    _⊎'_    : Choice → Choice → Choice
    subset' : (E : Choice) →  (ChoiceSet E → Bool) → Choice
    Σ'      : (E : Choice) →  (ChoiceSet E → Choice) → Choice

  ChoiceSet : Choice → Set 
  ChoiceSet ⊤' = ⊤ 
  ChoiceSet ∅' = ∅
  ChoiceSet Bool' = Bool
  ChoiceSet (E ×' F) = ChoiceSet E × ChoiceSet F
  ChoiceSet (E ⊎' F) = ChoiceSet E ⊎ ChoiceSet F
  ChoiceSet (subset' E f) = subset (ChoiceSet E) f
  ChoiceSet (Σ' A B) = Σ[ x ∈ ChoiceSet A ] ChoiceSet (B x) 


record  Process : Set where
  coinductive
  field
    E   : Choice
    Lab : ChoiceSet E → Label
    PE  : ChoiceSet E → Process
    I   : Choice
    PI  : ChoiceSet I → Process   


open Process

_|||_ : Process → Process → Process
E   (P ||| Q)         = E P ⊎' E Q
Lab (P ||| Q) (inl x) = Lab P x
Lab (P ||| Q) (inr x) = Lab Q x
PE  (P ||| Q) (inl x) = PE P x  ||| Q
PE  (P ||| Q) (inr x) = P       ||| PE Q x
I   (P ||| Q)         = I P ⊎' I Q
PI  (P ||| Q) (inl x) = PI P x  ||| Q
PI  (P ||| Q) (inr x) = P       ||| PI Q x


record Stream (i : Size) : Set where
  coinductive
  constructor cons'
  field
    head  :  ℕ 
    tail  :  {j : Size< i} → Stream j

open Stream


cons : ∀ {i} → ℕ →  Stream i → Stream (↑ i) 
head  (cons n s)  =  n
tail  (cons n s)  =  s



_+s_ : ∀ {i} → Stream i → Stream i → Stream i
head  (s  +s  s')  =  head  s  +   head  s'
tail  (s  +s  s')  =  tail  s  +s  tail  s'


fib : ∀ {i} → Stream i
head  fib         =  1
head  (tail fib)  =  1
tail  (tail fib)  =  fib +s tail fib


