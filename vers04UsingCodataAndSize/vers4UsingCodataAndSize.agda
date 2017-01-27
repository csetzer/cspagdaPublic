{-# OPTIONS --copatterns #-}

module CSPAgdaWithCoDatanotation4V where

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



----------------------Process--------------------------

mutual
   record ∞Process (i : Size) (A : Set) : Set where
     coinductive
     field
       force : (j : Size< i) → Process j A

   
   data Process (i : Size) ( A : Set ) : Set where
       node : (E   : Choice  ) 
           → (Lab : ChoiceSet E → Label)
           → (PE  : ChoiceSet E → ∞Process i A) 
           → (I   : Choice)
           → (PI  : ChoiceSet I → ∞Process i A)
           → Process i A
       terminate : A → Process i A

open ∞Process

delay : (i : Size) →  {A : Set} → Process i A  → ∞Process (↑ i) A
force (delay i p) j = p



-----------------------------------------Process+--------------------------------------------------------


data Process+ (i : Size) ( A : Set ) : Set where
       node : (E   : Choice  ) 
           → (Lab : ChoiceSet E → Label)
           → (PE  : ChoiceSet E → ∞Process i A) 
           → (I   : Choice)
           → (PI  : ChoiceSet I → ∞Process i A)
           → Process+ i A
       

---------  Sequential Composition (bind) -----


mutual 
   _>>_ : {i : Size} →  {A : Set} → {B : Set} → ∞Process i  A  → (A → ∞Process i B) → ∞Process i B
   force (_>>_ {i} x y) j  =   _>>'_ {j} (force x j)  y

   _>>'_ : {i : Size} → {A : Set} → {B : Set} → Process i  A  → (A → ∞Process (↑ i) B) → Process i B
   node E Lab PE I PI >>' Y = node E Lab (λ x → PE x >> Y) I (λ x → PI x >> Y) 
   _>>'_ {i} (terminate x)  Y = force (Y x) i -- Y x



---------------- Stop Operation ------------------


STOP : (i : Size) → {A : Set} →  A → ∞Process i A
force (STOP i a) j =  terminate a


----------------- Deadlock -----------------------


Deadlock : (i : Size) → {A : Set} →  ∞Process i A
force (Deadlock i) j = node ∅' efq efq ∅' efq



----------------- SKIP Operation -------------------


SKIP : (i : Size) → {A : Set} →  A →  ∞Process i A
force (SKIP  i a) j = node ∅' efq efq ⊤' (λ _ → delay i (terminate a))
 

---------------------------  Prefix -------------------

_⟶_ : {i : Size} → {A : Set} → Label → ∞Process i A → ∞Process (↑ i) A 
force (_⟶_ {i} a P) j = node ⊤' (λ x → a) (λ x → P) ∅' efq


--------------------------- Rec ------------------------


_>>=+_ : {i : Size} → {A B : Set} → Process+ i A → (A → ∞Process i B) → Process i B
_>>=+_ {i} (node E Lab PE I PI)  q = node E Lab (λ x → PE x >> q) I (λ x → PI x >> q)


mutual
  rec  : (i : Size) → {A B : Set} → (A → Process+ i (A + B)) → A → ∞Process i B
  force (rec i {A} {B} f a) j = f a >>=+ recaux j f

  recaux  : (i : Size) → {A B : Set} → (A → Process+ i (A + B)) → (A + B) → ∞Process i B
  recaux i f (inl a') = rec i f a'
  recaux i f (inr b) = delay i (terminate b)



---- Internal Choice Operation -------------



IntChoice : (i : Size) → {A : Set} → (I : Choice) 
          → (PI : ChoiceSet I → ∞Process i A) 
          → ∞Process i A 
force (IntChoice i I PI) j = node ∅' efq efq I (λ x → PI x) 


------  Renaming the Result returned ----------


mutual 
  fmap : (i : Size) → {A B : Set} → (A → B) → ∞Process i A → ∞Process i B
  force (fmap i f x )  j = fmap' j f (force x j)

  fmap' :  (i : Size) → {A B : Set} → (A → B) → Process i A → Process i B  
  fmap' i f (node E Lab PE I PI) = node E Lab (λ x → fmap i f (PE x)) I (λ x → fmap i f (PI x))
  fmap' i f (terminate x) = terminate (f x)



-------Parallel Operation -----------------------

mutual
   Parallel : (i : Size)
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → (A B : Set)
          → ∞Process i A
          → ∞Process i B
          → ∞Process i (A × B)

   force (Parallel i indepP indepQ interLeaved interLeavedToLabel A B P Q) j =
          Parallel' j indepP indepQ interLeaved interLeavedToLabel A B (force P j) (force Q j)  


   Parallel' : (i : Size)
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          
          → (A B : Set)
          → Process i A
          → Process i B
          → Process i (A × B)


   Parallel' i indepP indepQ interLeaved interLeavedToLabel A B (node E₁ Lab₁ PE₁ I₁ PI₁) (node E₂ Lab₂ PE₂ I₂ PI₂) = node E' Lab' PE' I' PI'  where
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
           Lab' (inr (sub (e₁ , e₂) cond)) = interLeavedToLabel (Lab₁ e₁) (Lab₂ e₂) cond

                                                  
           PE' : ChoiceSet E' → ∞Process i (A × B)                                                          --(♭(PE₁ e))
           force (PE' (inl (inl (sub e x)))) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                                                    (force (PE₁ e) j) (node E₂ Lab₂ PE₂ I₂ PI₂)
           force (PE' (inl (inr (sub e x)))) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                                                    (node E₁ Lab₁ PE₁ I₁ PI₁) (force (PE₂ e) j)
           force (PE' (inr (sub (e₁ , e₂) x))) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                                                      (force (PE₁ e₁) j) (force (PE₂ e₂) j)

           I' : Choice 
           I' = I₁ +' I₂

           PI' : ChoiceSet I' → ∞Process i (A × B)
           force (PI' (inl x)) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                                                    (force (PI₁ x) j) (node E₂ Lab₂ PE₂ I₂ PI₂)
           force (PI' (inr x)) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                                                    (node E₁ Lab₁ PE₁ I₁ PI₁) (force (PI₂ x) j)

   Parallel' i indepP indepQ interLeaved interLeavedToLabel A B (node E₁ Lab₁ PE₁ I₁ PI₁) (terminate b) = node E₁ Lab₁ PE' I₁ PI'
       where
         PE' : ChoiceSet E₁ → ∞Process i (A × B)
         force (PE' e) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B (force (PE₁ e) j) (terminate b) 
        
         PI' : ChoiceSet I₁ → ∞Process i (A × B)
         force (PI' i') j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B (force (PI₁ i') j) (terminate b)
   
   Parallel' i indepP indepQ interLeaved interLeavedToLabel A B (terminate a) (node E₂ Lab₂ PE₂ I₂ PI₂) = node E₂ Lab₂ PE' I₂ PI'
       where
        PE' : ChoiceSet E₂ → ∞Process i (A × B) 
        force (PE' e) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                            (terminate a) (force (PE₂ e) j)

        PI' : ChoiceSet I₂ → ∞Process i (A × B)
        force (PI' i') j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                            (terminate a) (force (PI₂ i') j)   
   Parallel' i indepP indepQ interLeaved interLeavedToLabel A B (terminate a) (terminate b) = terminate (a , b)         


--------------------------- Binary External Choice ------------------



mutual 
   extCh : (i : Size) →  {A : Set} → {B : Set} → ∞Process i  A  → ∞Process i B → ∞Process i ((A + B) + (A × B)) 
   force (extCh i x y) j  =   extCh' j (force x j) (force y j) 

   extCh' : (i : Size) → {A : Set} → {B : Set} → Process i  A  →  Process i B → Process i ((A + B) + (A × B))
   extCh' i (node E Lab PE I PI) (node E₁ Lab₁ PE₁ I₁ PI₁)  = node E' Lab' PE' I' PI' where
                                                   E' : Choice 
                                                   E' = E +' E₁

                                                   I' : Choice
                                                   I' = I +' I₁ 

                                                   Lab' :  ChoiceSet E' → Label
                                                   Lab' (inl x) = Lab x
                                                   Lab' (inr x) = Lab₁ x
                                                   
                                                   PE'  : ChoiceSet E' → ∞Process i ((_ + _) + (_ × _))
                                                   force (PE' (inl x)) i = (fmap' i (inl ∘ inl) (force (PE x) i))    
                                                   force (PE' (inr x)) i = (fmap' i (inl ∘ inr) (force (PE₁ x) i))    
                                                     

                                                   PI' : ChoiceSet I' → ∞Process i ((_ + _) + (_ × _))      
                                                   force (PI' (inl x)) i = extCh' i (force (PI x) i) (node E₁ Lab₁ PE₁ I₁ PI₁) 
                                                   force (PI' (inr x)) i = (extCh' i (node E Lab PE I PI) (force (PI₁ x) i)) 
                                                  

   extCh' i (node E Lab PE I PI) (terminate x) = terminate (inl (inr x))
   extCh' i (terminate x) (node E Lab PE I PI) = terminate (inl (inl x))
   extCh' i (terminate x) (terminate x₁) = terminate (inr (x , x₁)) 




------------- INTERUPT OPERATION -----------------------------------------------

mutual 
   Interrupt : (i : Size) →  {A : Set} → {B : Set} → ∞Process i  A  → ∞Process i B → ∞Process i ((A + B) + (A × B)) 
   force (Interrupt i x y) j  =   Interrupt' j (force x j)  (force y j)

   Interrupt' : (i : Size) → {A : Set} → {B : Set} → Process i  A  →  Process i B → Process i ((A + B) + (A × B))
   Interrupt' i (node E Lab PE I PI)  (node E₁ Lab₁ PE₁ I₁ PI₁)  = node E' Lab' PE' I' PI' where
                                                   E' : Choice 
                                                   E' = E +' E₁

                                                   I' : Choice
                                                   I' = I +' I₁ 

                                                   Lab' :  ChoiceSet E' → Label
                                                   Lab' (inl x) = Lab x
                                                   Lab' (inr x) = Lab₁ x
                                           
                                                   PE'  : ChoiceSet E' → ∞Process i ((_ + _) + (_ × _))    --PE₁   --PI₁
                                                   force (PE' (inl x)) i  = Interrupt' i (force (PE x) i) (node E₁ Lab₁ PE₁ I₁ PI₁)
                                                   force (PE' (inr x)) i = fmap' i (inl ∘ inr) (force (PE₁ x) i)

                                                   PI' : ChoiceSet I' → ∞Process i ((_ + _) + (_ × _))    --PE₁       --PI₁
                                                   force (PI' (inl x)) i = Interrupt' i (force (PI x) i) (node E₁ Lab₁ PE₁ I₁ PI₁)
                                                   force (PI' (inr x)) i = Interrupt' i (node E Lab PE I PI) (force (PI₁ x) i)

   Interrupt' i (node _ _ _ _ _) (terminate x) = terminate (inl (inr x))
   Interrupt' i (terminate x) (node _ _ _ _ _) = terminate (inl (inl x))
   Interrupt' i (terminate x) (terminate x₁) = terminate (inr (x , x₁)) 
           

------------- Renaming ---------------------


mutual 
   Rename :  (i : Size) → {A : Set} → (f : Label → Label) → ∞Process i A  → ∞Process i A
   force (Rename i f a) j = Rename' j f (force a j)
   
   Rename' : (i : Size) → {A : Set} → (f : Label → Label) → Process i A  → Process i A
   Rename' i f (node E Lab PE I PI) = node E (f ∘ Lab) (λ x → PE x ) I (λ x → PI x)
   Rename' i f (terminate x) = terminate x



-------------- Hide ---------------------

mutual 
   Hide : (i : Size) → {A : Set} → (hide : Label → Bool) → ∞Process i A → ∞Process i A
   force (Hide i f  P) j = Hide' j f (force P j)

   Hide' :  (i : Size) → {A : Set} → (hide : Label → Bool) → Process i A → Process i A
   Hide' i f (node E Lab PE I PI) = node (subset' E (¬b ∘ (f ∘ Lab))) (Lab ∘ projSubset) (λ x → Hide i f (PE (projSubset x))) (I +' subset'  E (f ∘ Lab)) (λ x → Hide i f (PI' i x)) where
                       PI' : (i : Size) → ChoiceSet  (I +' subset' E (f ∘ Lab)) →  (∞Process i _)
                       PI' i (inl x) = {!!}                        --PI x
                       PI' i (inr x) = {!!}                        --PE (projSubset x)
               

   Hide' i f (terminate x) = terminate x
 


