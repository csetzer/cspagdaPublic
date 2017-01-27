module CSPAgda where

open import Coinduction using (♯_ ; ♭ ; ∞)
open import Data.Nat using (ℕ;suc;zero)

--------------------- We introduce general Basic Types and Functions -------------

data Bool : Set where
  tt ff : Bool

data ⊤ : Set where 
 triv : ⊤ 

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥ 

data ∅ : Set where

-- ex falsum quodlibet (pattern matching on the empty pattern)
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


data subset (A : Set) (f : A → Bool) : Set where
  sub : (a : A) → True (f a) → subset A f

data Σ (A : Set) (B : A → Set) : Set where
  _,,_  : (a : A) → B a → Σ A B      


-- the following code Σ-syntax
-- allows to use 
-- Σ[ x ∈ A ] B 
-- for what in type theory is written Σ x: A.B
-- and normally would need  to be written as Σ A (λ x → B)

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



--------------------- Labels will be postulated here ---------------------
--------------------- they could as well be taken as a parameter ---------


postulate Label : Set 


---  We introduce the universes for choice sets for external and internal choice -----


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

----------------------------------------Process----------------------------------------------------------


data Process ( A : Set ) : Set where
 node : (E   : Choice) 
     → (Lab : ChoiceSet E → Label)
     → (PE  : ChoiceSet E → ∞ (Process A)) 
     → (I   : Choice)
     → (PI  : ChoiceSet I → ∞ (Process A))
     → Process A
 terminate : A → Process A

-----------------------------------------Process+--------------------------------------------------------

-- Process+ A will be like Process, but have at least one interaction.

data Process+ ( A : Set ) : Set where
 node : (E   : Choice) 
     → (Lab : ChoiceSet E → Label)
     → (PE  : ChoiceSet E → Process A) 
     → (I   : Choice)
     → (PI  : ChoiceSet I → Process A)
     → Process+ A


----------------------------------------- Stop Operation ------------------------------------------------------


STOP : {A : Set} →  A → Process A
STOP a = terminate a

----------------- Deadlock -----------------------

Deadlock : {A : Set} →  Process A
Deadlock = node ∅' efq efq ∅' efq


----------------------------------------- SKIP Operation ------------------------------------------------------


SKIP : {A : Set} →  A →  Process A
SKIP a = node ∅' efq efq ⊤' (λ _ → ♯ terminate a)


---------------------------  Prefix ----------------------

_⟶_ : {A : Set} → Label → Process A → Process A 
a ⟶ P = node ⊤' (λ x → a) (λ x → ♯ P) ∅' efq

---------------------- Sequential Composition (bind) --------------------------------------------

_>>_ : {A B : Set}
       →  Process A  
       → (A → Process B) 
       → Process B
node E Lab PE I PI >> Y = node E Lab 
                               (λ x → ♯ (♭ (PE x) >> Y)) 
                               I 
                               (λ x → ♯ (♭ (PI x) >> Y))
terminate x        >> Y = Y x   


-------------------- Recursion where loop needs to have at least one transition ----

mutual
  rec  : {A B : Set}
         → (A → Process+ (A + B))
         → A → Process B
--  rec f a  = rec₁  (f a) f
  rec f a with f a
  ... | (node E Lab PE I PI) 
      = node E Lab 
                 (λ x → ♯ rec'  (PE x) f) 
                 I 
                 (λ x → ♯ rec'  (PI x) f)

  
  rec' : {A B : Set} 
         →  Process (A + B) 
         →  (A →  Process+ (A + B)) 
         → Process B
  rec' (node E Lab PE I PI) f 
          = node E Lab 
                 (λ x → ♯ rec'  (♭ (PE x)) f) 
                 I 
                 (λ x → ♯ rec'  (♭ (PI x)) f)
  rec' (terminate (inl a)) f = rec f a 
  rec' (terminate (inr b)) f = terminate b





----------------------------------------- Internal Choice Operation --------------------------------------------


IntChoice : {A : Set} → (I : Choice) 
          → (PI : ChoiceSet I → Process A) 
          → Process A 
IntChoice I PI  = node ∅' efq efq I (λ x → ♯ PI x) 


---------------------  Renaming the Result returned --------------------------------------------


fmap : {A B : Set} → (A → B) → Process A → Process B
fmap f (node E Lab PE I PI) = node E Lab 
                                   (λ x → ♯ fmap f (♭ (PE x))) 
                                   I 
                                   (λ x → ♯ fmap f (♭ (PI x)))
fmap f (terminate x) = terminate (f x)



--------------------------------Parallel Operation ------------------------------------------------------




Parallel :  (indepP indepQ : Label → Bool)
         → (interLeaved : Label → Label → Bool)
         → (interLeavedToLabel : (PLab QLab : Label) 
                                  → True (interLeaved PLab QLab)
                                  → Label)
         → (A B : Set)
         → Process A
         → Process B
         → Process (A × B)

Parallel   indepP indepQ interLeaved interLeavedToLabel 
           A B
           (node E₁ Lab₁  PE₁ I₁ PI₁) 
           (node E₂ Lab₂  PE₂ I₂ PI₂) 
         = node E' Lab' PE' I' PI'
         where
           E₁' : Choice 
           E₁' = subset' E₁ (indepP ∘ Lab₁) +' subset' E₂ (indepQ ∘ Lab₂)

           f₁ : ChoiceSet (E₁ ×' E₂) →  Bool
           f₁ ( e₁ , e₂ ) = interLeaved (Lab₁ e₁) (Lab₂ e₂)

           E₂' : Choice
           E₂' = subset' (E₁ ×' E₂) f₁

           E' : Choice
           E' = E₁' +' E₂'

           Lab' : ChoiceSet E' →  Label
           Lab' (inl (inl (sub e _)))  = Lab₁ e
           Lab' (inl (inr (sub e _)))  = Lab₂ e
           Lab' (inr (sub (e₁ , e₂) cond)) = interLeavedToLabel 
                                            (Lab₁ e₁) (Lab₂ e₂) cond

           PE' : ChoiceSet E' →  ∞ (Process (A × B))
           PE' (inl (inl (sub e _)))  
                = ♯ Parallel indepP indepQ interLeaved 
                              interLeavedToLabel  A B
                              (♭ (PE₁ e)) 
                              (node E₂ Lab₂ PE₂ I₂ PI₂)

           PE' (inl (inr (sub e _)))  
                = ♯ Parallel indepP indepQ interLeaved 
                            interLeavedToLabel A B  
                            (node E₁ Lab₁ PE₁ I₁ PI₁) 
                            (♭ (PE₂ e))

           PE' (inr (sub (e₁ , e₂) _)) 
               = ♯ Parallel indepP indepQ interLeaved 
                            interLeavedToLabel A B
 
                            (♭ (PE₁ e₁)) 
                            (♭ (PE₂ e₂))
           I' : Choice 
           I' = I₁ +' I₂

           PI' :  ChoiceSet I' → ∞ (Process (A × B))
           PI' (inl x) 
               = ♯ Parallel indepP indepQ interLeaved 
                            interLeavedToLabel A B
                            (♭ (PI₁ x)) 
                            (node E₂ Lab₂ PE₂ I₂ PI₂)
           PI' (inr x) 
               = ♯ Parallel indepP indepQ interLeaved 
                            interLeavedToLabel A B 
                            (node E₁ Lab₁ PE₁ I₁ PI₁) 
                            (♭ (PI₂ x))

Parallel   indepP indepQ interLeaved interLeavedToLabel A B
           (node E₁ Lab₁ PE₁ I₁ PI₁) 
           (terminate b) 
         =  node E₁ Lab₁ PE' I₁ PI' 
         where 
          PE' :  ChoiceSet E₁ → ∞ (Process (A × B))
          PE' e  = ♯ Parallel indepP indepQ interLeaved 
                              interLeavedToLabel A B 
                              (♭ (PE₁ e)) 
                              (terminate b)

          PI' :  ChoiceSet I₁ → ∞ (Process (A × B))
          PI' i  = ♯ Parallel indepP indepQ interLeaved 
                              interLeavedToLabel A B 
                              (♭ (PI₁ i)) 
                              (terminate b)


Parallel   indepP indepQ interLeaved interLeavedToLabel A B
           (terminate a) 
           (node E₂ Lab₂ PE₂ I₂ PI₂) 
         =  node E₂ Lab₂ PE' I₂ PI'
         where 
          PE' :  ChoiceSet E₂ → ∞ (Process (A × B))
          PE' e  = ♯ Parallel indepP indepQ interLeaved 
                              interLeavedToLabel  A B
                              (terminate a) 
                              (♭ (PE₂ e)) 

          PI' :  ChoiceSet I₂ → ∞ (Process (A × B))
          PI' i  = ♯ Parallel indepP indepQ interLeaved 
                              interLeavedToLabel A B 
                              (terminate a) 
                              (♭ (PI₂ i)) 

Parallel   indepP indepQ interLeaved interLeavedToLabel A B 
           (terminate a) 
           (terminate b) 
         = terminate (a , b)





--------------------------- Binary External Choice ------------------



ExtChoice : {A B : Set} 
                 → Process A 
                 → Process B  
                 → Process ((A + B) + (A × B))
ExtChoice {A} {B} (node E₁ Lab₁ PE₁ I₁ PI₁) (node E₂ Lab₂ PE₂ I₂ PI₂) 
         = node E' Lab' PE' I' PI' where

           E' : Choice
           E' = E₁ +' E₂ 

           I' : Choice
           I' = I₁ +' I₂

           Lab' : ChoiceSet E' → Label
           Lab' (inl x) = Lab₁ x
           Lab' (inr x) = Lab₂ x   

           PE' :   ChoiceSet E' → ∞ (Process ((A + B) + (A × B)))
           PE' (inl x) = ♯ fmap (inl ∘ inl) (♭ (PE₁ x))
           PE' (inr x) = ♯ fmap (inl ∘ inr) (♭ (PE₂ x))

           PI' :   ChoiceSet I' → ∞ (Process ((A + B) + (A × B)))
           PI' (inl x) = ♯ ExtChoice (♭ (PI₁ x)) (node E₂ Lab₂ PE₂ I₂ PI₂)
           PI' (inr x) = ♯ ExtChoice (node E₁ Lab₁ PE₁ I₁ PI₁) (♭ (PI₂ x))

           
ExtChoice (node E₁ Lab₁ PE₁ I₁ PI₁) (terminate b) 
  = terminate (inl (inr b))

--  =  node E₁ Lab₁ PE' I₁ PI' where
--
--    PE' : ChoiceSet E₁ → ∞ (Process ((A + B) + (A × B)))
--    PE' e  = ♯ ExtChoice (♭ (PE₁ e)) (terminate b) 
--
--    PI' : ChoiceSet I₁ → ∞ (Process ((A + B) + (A × B)))
--    PI' i = ♯ ExtChoice (♭ (PI₁ i)) (terminate b)

ExtChoice (terminate a) (node E₂ Lab₂ PE₂ I₂ PI₂) 
  = terminate (inl (inl a))

--  = node E₂ Lab₂ PE' I₂ PI' where
--
--    PE' : ChoiceSet E₂ → ∞ (Process ((A + B) + (A × B)))
--    PE' e = ♯ ExtChoice (terminate a) (♭ (PE₂ e))
--
--    PI'  : ChoiceSet I₂ → ∞ (Process ((A + B) + (A × B)))
--    PI' i  = ♯ ExtChoice (terminate a) (♭ (PI₂ i))  

ExtChoice (terminate a) (terminate b) = terminate (inr (a , b))


------------- INTERUPT OPERATION -----------------------------------------------



Interupt : {A B : Set} 
          → Process A 
          → Process B  
          → Process ((A + B) + (A × B))
Interupt {A} {B} (node E₁ Lab₁ PE₁ I₁ PI₁) (node E₂ Lab₂ PE₂ I₂ PI₂) 
    = node E' Lab' PE' I' PI' where

      E' : Choice
      E' = E₁ +' E₂

      Lab' : ChoiceSet E' → Label
      Lab' (inl x) = Lab₁ x
      Lab' (inr x) = Lab₂ x

      I' : Choice
      I' = I₁ +' I₂

      PE' :   ChoiceSet E' → ∞ (Process ((A + B) + (A × B)))
      PE' (inl x) = ♯ Interupt (♭ (PE₁ x))  (node E₂ Lab₂ PE₂ I₂ PI₂) 
      PE' (inr x) = ♯ fmap (inl ∘ inr) (♭ (PE₂ x))

      PI' :  ChoiceSet I' → ∞ (Process ((A + B) + (A × B)))
      PI' (inl x) = ♯ Interupt (♭ (PI₁ x)) (node E₂ Lab₂ PE₂ I₂ PI₂)
      PI' (inr x) = ♯ Interupt (node E₁ Lab₁ PE₁ I₁ PI₁) (♭ (PI₂ x))

Interupt (node _ _ _ _ _) (terminate b)    = terminate (inl (inr b))
Interupt (terminate a)    (node _ _ _ _ _) = terminate (inl (inl a))
Interupt (terminate a)    (terminate b)    = terminate (inr (a , b))


----------------------------------------- Renaming --------------------------------------------

Rename : {A : Set} → (f : Label → Label) → Process A  → Process A
Rename f (node E Lab PE I PI) 
       = node E (f ∘ Lab) 
              (λ x → ♯ Rename f (♭ (PE x))) 
              I 
              (λ x → ♯ Rename f (♭ (PI x)))
Rename f (terminate a) = terminate a


----------------------------------------- Hide --------------------------------------------

Hide : {A : Set} → (hide : Label → Bool) → Process A → Process A 
Hide hide (node E Lab PE I PI) 
     = node (subset' E (¬b ∘ (hide ∘ Lab))) 
            (Lab ∘ projSubset)
            (λ x → ♯ Hide hide (♭ (PE (projSubset x)))) 
            (I +' subset' E (hide ∘ Lab))
            (λ x → ♯ Hide hide  (♭ ( PI' x )))
 where
  PI' : ChoiceSet  (I +' subset' E (hide ∘ Lab)) 
          → ∞ (Process _)
  PI' (inl x) = PI x
  PI' (inr x) = PE (projSubset x)

Hide hide (terminate x) = terminate x



