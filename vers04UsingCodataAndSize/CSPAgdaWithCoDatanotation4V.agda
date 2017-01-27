{-# OPTIONS --copatterns #-}

module CSPAgdaWithCoDatanotation4v where

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



----------------------Processx--------------------------

mutual
   record ∞Processx (i : Size) (A : Set) : Set where
     coinductive
     field
       forcex : (j : Size< i) → Processx j A

   
   data Node (i : Size) (A : Set) : Set where
       thenode : (E   : Choice  ) 
           → (Lab : ChoiceSet E → Label)
           → (PE  : ChoiceSet E → ∞Processx i A) 
           → (I   : Choice)
           → (PI  : ChoiceSet I → ∞Processx i A)
           → Node i A


   data Processx (i : Size) ( A : Set ) : Set where
     node : Node i A -> Processx i A
     terminate : A → Processx i A

open ∞Processx

delayx : (i : Size) →  {A : Set} → Processx i A  → ∞Processx (↑ i) A
forcex (delayx i p) j = p


node2E : {i : Size} {A : Set} (P : Node i A) →  Choice
node2E (thenode E Lab PE I PI) = E

Node2E : {i : Size} {A : Set} (P : Node i A) →  Set
Node2E P = ChoiceSet (node2E P)

node2Lab : {i : Size} {A : Set} (P : Node i A) → Node2E P → Label
node2Lab (thenode E Lab PE I PI) = Lab

node2PE : {i : Size} {A : Set} (P : Node i A) → Node2E P → ∞Processx i A 
node2PE (thenode E Lab PE I PI) = PE

node2I : {i : Size} {A : Set} (P : Node i A) →  Choice
node2I (thenode E Lab PE I PI) = I

Node2I : {i : Size} {A : Set} (P : Node i A) →  Set
Node2I P = ChoiceSet (node2I P)

node2PI : {i : Size} {A : Set} (P : Node i A) → Node2I P → ∞Processx i A 
node2PI (thenode E Lab PE I PI) = PI


-----------------------------------------Process+--------------------------------------------------------


data Process+ (i : Size) ( A : Set ) : Set where
       node : (E   : Choice  ) 
           → (Lab : ChoiceSet E → Label)
           → (PE  : ChoiceSet E → ∞Process i A) 
           → (I   : Choice)
           → (PI  : ChoiceSet I → ∞Process i A)
           → Process+ i A
       

----------------------------Sequential Composition (bind)------------------------------------


mutual 
   _>>_ : {i : Size} →  {A : Set} → {B : Set} → ∞Process i  A  → (A → ∞Process i B) → ∞Process i B
   force (_>>_ {i} x y) j  =   _>>'_ {j} (force x j)  y

   _>>'_ : {i : Size} → {A : Set} → {B : Set} → Process i  A  → (A → ∞Process (↑ i) B) → Process i B
   node E Lab PE I PI >>' Y = node E Lab (λ x → PE x >> Y) I (λ x → PI x >> Y) 
   _>>'_ {i} (terminate x)  Y = force (Y x) i -- Y x



_∵_ : {i : Size} →
      {A : Set} →
      {B : Set} → ∞Process i A → (A → ∞Process i B) → ∞Process i B
_∵_ = _>>_ 


_∵'_ : {i : Size} →
       {A : Set} →
       {B : Set} → Process i A → (A → ∞Process (↑ i) B) → Process i B
_∵'_ =  _>>'_ 
---------------- Stop Operation ------------------


STOP : (i : Size) → {A : Set} →  A → ∞Process i A
force (STOP i a) j =  terminate a


Stop :  {i : Size} → {A : Set} →  A → ∞Process i A
Stop = STOP _

----------------- Deadlock -----------------------


Deadlock : (i : Size) → {A : Set} →  ∞Process i A
force (Deadlock i) j = node ∅' efq efq ∅' efq



----------------- SKIP Operation -------------------


SKIP : (i : Size) → {A : Set} →  A →  ∞Process i A
force (SKIP  i a) j = node ∅' efq efq ⊤' (λ _ → delay i (terminate a))
 

Skip :  {i : Size} -> {A : Set} → A → (∞Process i A)
Skip = SKIP _

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

R :  {i : Size} → {A B : Set} → (A → Process+ i (A + B)) → A → ∞Process i B
R = rec _

R' : {i : Size} → {A B : Set} → (A → Process+ i (A + B)) → (A + B) → ∞Process i B
R' = recaux _

---- Internal Choice Operation -------------



IntChoice : (i : Size) → {A : Set} → (I : Choice) 
          → (PI : ChoiceSet I → ∞Process i A) 
          → ∞Process i A 
force (IntChoice i I PI) j = node ∅' efq efq I (λ x → PI x) 



Int : {i : Size} → {A : Set} → (I : Choice) 
       → (PI : ChoiceSet I → ∞Process i A) 
       → ∞Process i A 
Int = IntChoice _



------  Renaming the Result returned ----------


mutual 
  fmap : (i : Size) → {A B : Set} → (A → B) → ∞Process i A → ∞Process i B
  force (fmap i f x )  j = fmap' j f (force x j)

  fmap' :  (i : Size) → {A B : Set} → (A → B) → Process i A → Process i B  
  fmap' i f (node E Lab PE I PI) = node E Lab (λ x → fmap i f (PE x)) I (λ x → fmap i f (PI x))
  fmap' i f (terminate x) = terminate (f x)




------  Renaming the Result returned ----------


mutual 
  fmapx : (i : Size) → {A B : Set} → (A → B) → ∞Processx i A → ∞Processx i B
  forcex (fmapx i f x )  j = fmapx' j f (forcex x j)

  fmapx'' : (i : Size) → {A B : Set} → (A → B) → Node i A → Node i B  
  fmapx'' i f (thenode E Lab PE I PI) = thenode E Lab (λ x → fmapx i f (PE x)) I (λ x → fmapx i f (PI x))

  fmapx' :  (i : Size) → {A B : Set} → (A → B) → Processx i A → Processx i B  
  fmapx' i f (node P) = node (fmapx'' i f P)
  fmapx' i f (terminate x) = terminate (f x)



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

                                                  
           PE' : ChoiceSet E' → ∞Process i (A × B)                                                         
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






parallel : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label)
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → (A B : Set)
          → ∞Process i A
          → ∞Process i B
          → ∞Process i (A × B)

parallel = Parallel _ 


parallel' : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          
          → (A B : Set)
          → Process i A
          → Process i B
          → Process i (A × B)

parallel' = Parallel' _

---------------------------Parallel---------------------------------

mutual
   Parallelx : (i : Size)
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → (A B : Set)
          → ∞Processx i A
          → ∞Processx i B
          → ∞Processx i (A × B)

   forcex (Parallelx i indepP indepQ interLeaved interLeavedToLabel A B P Q) j =
          Parallelx' j indepP indepQ interLeaved interLeavedToLabel A B (forcex P j) (forcex Q j)  


   Parallelx' : (i : Size)
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → (A B : Set)
          → Processx i A
          → Processx i B
          → Processx i (A × B)


   Parallelx' i indepP indepQ interLeaved interLeavedToLabel A B (node P) (node Q) = node (ParNode indepP indepQ interLeaved interLeavedToLabel P Q)  
   Parallelx' i indepP indepQ interLeaved interLeavedToLabel A B (node (thenode E Lab PE I PI)) (terminate Q) = node (ParNode₁ indepP indepQ interLeaved interLeavedToLabel (thenode E Lab PE I PI) (terminate Q)) 
            

   Parallelx' i indepP indepQ interLeaved interLeavedToLabel A B (terminate P) (node (thenode E Lab PE I PI)) =  node (ParNode₂ indepP indepQ interLeaved interLeavedToLabel (terminate P) (thenode E Lab PE I PI)) 

      
   Parallelx' i indepP indepQ interLeaved interLeavedToLabel A B (terminate P) (terminate Q) = terminate (P , Q)


   ParNode : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
                                   → Node i A → Node i B  → Node i (A × B)
   ParNode indepP indepQ interLeaved interLeavedToLabel P Q = thenode (parE indepP indepQ interLeaved interLeavedToLabel P Q) (parLab' indepP indepQ interLeaved interLeavedToLabel P Q) (parPEE' indepP indepQ interLeaved interLeavedToLabel P Q ) (I'' P Q) (parPI' indepP indepQ interLeaved interLeavedToLabel P Q)
       
   parE' : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Node i B)  → (indepP indepQ : Label → Bool) → Choice
   parE' {i} {A} {B} P Q indepP indepQ = subset' (node2E P) (indepP ∘ node2Lab P) +'
                 subset' (node2E Q) (indepQ ∘ node2Lab Q)

   f :   {i : Size} →
         {A B : Set} →
         (P : Node i A) →
         (Q : Node i B) → {interLeaved : Label → Label → Bool}
         → ChoiceSet (node2E P ×' node2E Q) → Bool
   f {i} {A} {B} P Q {interLeaved} ( e₁ , e₂ ) = interLeaved (node2Lab Q e₂) (node2Lab P e₁)


   f₁ :  {i : Size} →
         {A B : Set} →
         (P : Node i A) →
         (Q : Node i B) → (interLeaved : Label → Label → Bool)
         → ChoiceSet (node2E P) × ChoiceSet (node2E Q) → Bool
   f₁ P Q interLeaved (e , e₁) = interLeaved (node2Lab P e) (node2Lab Q e₁) 


   parE₂ :  {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → Node i A → Node i B → (interLeaved : Label → Label → Bool) → Choice
   parE₂ indepP indepQ interLeaved interLeavedToLabel P Q e = subset' (node2E P ×' node2E Q) (f₁ P Q e)

   parE :  {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → Node i A → Node i B → Choice
   parE indepP indepQ interLeaved interLeavedToLabel P Q  = parE' P Q indepP indepQ  +' parE₂ indepP indepQ interLeaved interLeavedToLabel P Q interLeaved 
    

   parLab' : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
                                   → (P : Node i A) → (Q : Node i B)  → ChoiceSet (parE indepP indepQ interLeaved interLeavedToLabel P Q) → Label
   parLab' indepP indepQ interLeaved interLeavedToLabel P Q (inl (inl (sub e x))) = node2Lab P e
   parLab' indepP indepQ interLeaved interLeavedToLabel P Q (inl (inr (sub e x))) = node2Lab Q e
   parLab' indepP indepQ interLeaved interLeavedToLabel P Q (inr (sub (e , e₁) x)) = interLeavedToLabel (node2Lab P e) (node2Lab Q e₁) x
  
                                
   parPEE' : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) →  (P : Node i A) → (Q : Node i B)
                                   →   ChoiceSet (parE indepP indepQ interLeaved interLeavedToLabel P Q)  → ∞Processx i (A × B)                              
   forcex (parPEE' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel (thenode E Lab PE I PI) Q (inl (inl (sub e x)))) j = Parallelx'   j indepP indepQ interLeaved interLeavedToLabel A B (forcex (PE e) j) (node Q)
   forcex (parPEE' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P (thenode E Lab PE I PI) (inl (inr (sub e x)))) j = Parallelx'   j indepP indepQ interLeaved interLeavedToLabel A B (node P) (forcex (PE e) j)
   forcex (parPEE' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁) (inr (sub    (e , e₁) x))) j = Parallelx' j indepP indepQ interLeaved interLeavedToLabel A B (forcex (PE e) j) (forcex (PE₁ e₁) j)

   I'' :  {i : Size} → {A B : Set} → Node i A →  Node i B → Choice
   I''  P Q =  (node2I P)  +'  (node2I Q)

   parPI' : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Node i A) → (Q : Node i B) →  ChoiceSet (I'' P Q) → ∞Processx i (A × B)
   forcex (parPI' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q (inl x)) j = Parallelx' j indepP indepQ interLeaved interLeavedToLabel A B (forcex (node2PI P x) j)  (node Q)
   forcex (parPI' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q (inr x)) j = Parallelx' j indepP indepQ interLeaved interLeavedToLabel A B  (node P) (forcex (node2PI Q x) j)

   ParNode₁ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
                                   → (P : Node i A) → (Q : Processx i B)  → Node i (A × B)
   ParNode₁ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q = thenode (parE₁ P (terminate Q)) (parLab₁ P Q) (parPE₁ indepP indepQ interLeaved interLeavedToLabel P Q) (parI₁ P (terminate Q)) (parPI₁ indepP indepQ interLeaved interLeavedToLabel P Q)

   parE₁ : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Processx i B) → Choice
   parE₁ {i} {A} {B}  P Q = node2E P

   parLab₁ : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Processx i B) → ChoiceSet (parE₁ P (terminate Q)) → Label
   parLab₁ P Q e = node2Lab P e 
  
   parPE₁ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Node i A) → (Q : Processx i B)
                                   → ChoiceSet (parE₁ P (terminate Q)) → ∞Processx i (A × B)
   parPE₁ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q  x  = Parallelx i indepP indepQ interLeaved interLeavedToLabel A B (delayx i (node P)) (delayx i  Q)

   parI₁ : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Processx i B) → Choice
   parI₁ {i} {A} {B}  P Q = node2I P




   parPI₁ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Node i A) → (Q : Processx i B)
                                   → ChoiceSet (parI₁ P (terminate Q)) → ∞Processx i (A × B)
   parPI₁ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q x  = Parallelx i indepP indepQ interLeaved interLeavedToLabel A B (delayx i (node P)) (delayx i  Q)




   ParNode₂ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
                                   → (P : Processx i A) → (Q : Node i B)  → Node i (A × B)
   ParNode₂ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q = thenode (parE'₂ (terminate P) Q) (parLab₂ P Q) (parPE₂ indepP indepQ interLeaved interLeavedToLabel P Q) (parI₂ (terminate P) Q) (parPI₂ indepP indepQ interLeaved interLeavedToLabel P Q)

   parE'₂ : {i : Size} → {A B : Set} → (P : Processx i A) → (Q : Node i B) → Choice
   parE'₂ {i} {A} {B}  P Q = node2E Q

   parLab₂ : {i : Size} → {A B : Set} → (P : Processx i A) → (Q : Node i B) → ChoiceSet (parE'₂ (terminate P) Q) → Label
   parLab₂ P Q e = node2Lab Q e 
  
   parPE₂ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Processx i A) → (Q : Node i B)
                                   → ChoiceSet (parE'₂ (terminate P)  Q) → ∞Processx i (A × B)
   parPE₂ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q  x  = Parallelx i indepP indepQ interLeaved interLeavedToLabel A B  (delayx i P) (delayx i (node Q))

   parI₂ : {i : Size} → {A B : Set} → (P : Processx i A) → (Q : Node i B) → Choice
   parI₂ {i} {A} {B}  P Q = node2I Q




   parPI₂ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Processx i A) → (Q : Node i B)
                                   → ChoiceSet (parI₂ (terminate P) Q) → ∞Processx i (A × B)
   parPI₂ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q x  = Parallelx i indepP indepQ interLeaved interLeavedToLabel A B (delayx i P) (delayx i (node Q))


parallelx : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → (A B : Set)
          → ∞Processx i A
          → ∞Processx i B
          → ∞Processx i (A × B)

parallelx = Parallelx _



parallelx' : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)          
          → (A B : Set)
          → Processx i A
          → Processx i B
          → Processx i (A × B)

parallelx'  =  Parallelx' _


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


_□''_ :  {i : Size} →  {A : Set} → {B : Set} → ∞Process i  A  → ∞Process i B → ∞Process i ((A + B) + (A × B)) 
_□''_ = extCh _

_□'''_ :  {i : Size} → {A : Set} → {B : Set} → Process i  A  →  Process i B → Process i ((A + B) + (A × B))
_□'''_ = extCh' _

--------------------------- Binary External Choice  xversion ------------------


mutual 
   extChx : (i : Size) →  {A : Set} → {B : Set} → ∞Processx i  A  → ∞Processx i B → ∞Processx i ((A + B) + (A × B)) 
   forcex (extChx i x y) j  =   extChx' j (forcex x j) (forcex y j) 

   extChx' : (i : Size) → {A : Set} → {B : Set} → Processx i  A  →  Processx i B → Processx i ((A + B) + (A × B))
   extChx' i {A} {B} (node P) (node Q)  = node (extChNode P Q)
   extChx' i (node (thenode E Lab PE I PI)) (terminate x) = terminate (inl (inr x))
   extChx' i (terminate x) (node (thenode E Lab PE I PI)) = terminate (inl (inl x))
   extChx' i (terminate x) (terminate x₁) = terminate (inr (x , x₁)) 

   extChNode : {i : Size} → {A B : Set} → Node i A → Node i B  → Node i ((A + B) + (A × B))
   extChNode P Q = thenode (extChE' P Q) (extChLab' P Q) (extChPE' P Q) (extChI' P Q) (extChPI' P Q)

   extChE' : {i : Size} → {A B : Set} → Node i A → Node i B  → Choice
   extChE' P Q = (node2E P) +' (node2E Q)


   extChLab' : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Node i B)  → ChoiceSet (extChE' P Q) → Label
   extChLab' P Q (inl x) = node2Lab P x
   extChLab' P Q (inr x) = node2Lab Q x

   extChPE'a : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Node i B)  
               → ChoiceSet (extChE' P Q) →  (j : Size< i) → Processx j ((A + B) + (A × B))
   extChPE'a {i} P Q (inl x) j = fmapx' j (inl ∘ inl) (forcex (node2PE P x) j)  
   extChPE'a {i} P Q (inr x) j = fmapx' j (inl ∘ inr) (forcex (node2PE Q x) j) 


   extChPE' : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Node i B)  
               → ChoiceSet (extChE' P Q) →  ∞Processx i ((A + B) + (A × B))
   forcex (extChPE' P Q x) j = extChPE'a P Q x j


   extChI' : {i : Size} → {A B : Set} → Node i A → Node i B  → Choice
   extChI'  P Q = (node2I P) +' (node2I Q)


   extChPI'toP : (i : Size) → (j : Size< i) → (A B : Set) → (P : Node i A) → (Q : Node i B)  
                  → ChoiceSet (extChI' P Q) →  Processx j A
   extChPI'toP i j A B P Q (inl x) = forcex (node2PI P x) j
   extChPI'toP i j A B P Q (inr x) = node P


   extChPI'toQ : (i : Size) → (j : Size< i) → (A B : Set) → (P : Node i A) → (Q : Node i B)  
                  → ChoiceSet (extChI' P Q) →  Processx j B
   extChPI'toQ i j A B P Q (inl x) = node Q
   extChPI'toQ i j A B P Q (inr x) = forcex (node2PI Q x) j


   extChPI' : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Node i B)  
               → ChoiceSet (extChI' P Q) →  ∞Processx i ((A + B) + (A × B))
   forcex (extChPI' {i}  {A} {B} P Q x) j = extChx' j (extChPI'toP i j A B P Q x) (extChPI'toQ i j A B P Q x)



_□_ : {i : Size} →  {A : Set} → {B : Set} → ∞Processx i  A  → ∞Processx i B → ∞Processx i ((A + B) + (A × B)) 
_□_ = extChx _ 

_□'_ : {i : Size} → {A : Set} → {B : Set} → Processx i  A  →  Processx i B → Processx i ((A + B) + (A × B))
_□'_ = extChx' _

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
           

_△_ : {i : Size} →  {A : Set} → {B : Set} → ∞Process i  A  → ∞Process i B → ∞Process i ((A + B) + (A × B)) 
_△_ = Interrupt _

_△'_ : {i : Size} → {A : Set} → {B : Set} → Process i  A  →  Process i B → Process i ((A + B) + (A × B))
_△'_ = Interrupt' _

------------- Renaming ---------------------


mutual 
   Rename :  (i : Size) → {A : Set} → (f : Label → Label) → ∞Process i A  → ∞Process i A
   force (Rename i f a) j = Rename' j f (force a j)
   
   Rename' : (i : Size) → {A : Set} → (f : Label → Label) → Process i A  → Process i A
   Rename' i f (node E Lab PE I PI) = node E (f ∘ Lab) (λ x → PE x ) I (λ x → PI x)
   Rename' i f (terminate x) = terminate x

rename : {i : Size} → {A : Set} → (f : Label → Label) → ∞Process i A  → ∞Process i A
rename = Rename _

rename' : {i : Size} → {A : Set} → (f : Label → Label) → Process i A  → Process i A
rename' = Rename' _

-------------- Hide ---------------------


mutual 
   Hide : (i : Size) → {A : Set} → (hide : Label → Bool) → ∞Process i A → ∞Process i A
   force (Hide i f  P) j = Hide' j f (force P j)

   Hide' : (i : Size) → {A : Set} → (hide : Label → Bool) → Process i A → Process i A
   Hide' i {A} f (node E Lab PE I PI) = node (subset' E (¬b ∘ (f ∘ Lab))) (Lab ∘ projSubset) (λ x → Hide i f (PE (projSubset x))) (I +' subset'  E (f ∘ Lab)) (λ x → Hide i {A} f (PI' x)) where   
          PI' : ChoiceSet  (I +' subset' E (f ∘ Lab)) → ∞Process i A
          PI' (inl x) = PI x
          PI' (inr x) = PE (projSubset x)
   Hide' i f (terminate x) = terminate x
  
                     
_/_ : {i : Size} → {A : Set} → (hide : Label → Bool) → ∞Process i A → ∞Process i A
_/_ = Hide _

_/'_ : {i : Size} → {A : Set} → (hide : Label → Bool) → Process i A → Process i A
_/'_ = Hide' _

-------------------------- Refinment---------------------

mutual
   
    record ∞Tr (i : Size) {A : Set} (l : List Label) (P : ∞Process  i A) : Set where
     coinductive
     field
       force' : (j : Size< i) → Tr j  l (force P j)

    data Tr (j : Size) {A : Set} : (l : List Label) -> (P : Process j A) -> Set where 
        empty : {P : Process j A} → Tr  j {A} [] P
        extchoice : {E   : Choice} 
         → {Lab : ChoiceSet E → Label}
         → {PE  : ChoiceSet E → ∞Process j A} 
         → {I   : Choice}
         → {PI  : ChoiceSet I → ∞Process j A}
         → (x : ChoiceSet E)
         → (l : List Label)
         → ∞Tr j {A} l (PE x)
         → Tr j {A} ((Lab x) :: l) (node E Lab PE I PI) 
        intchoice : {E   : Choice} 
         → {Lab : ChoiceSet E → Label}
         → {PE  : ChoiceSet E → ∞Process j A} 
         → {I   : Choice}
         → {PI  : ChoiceSet I → ∞Process j A}
         → (x : ChoiceSet I)
         → (l : List Label)
         → ∞Tr j {A} l (PI x)
         → Tr  j {A} l (node E Lab PE I PI) 

open ∞Tr


Refinement : (i : Size) {A B : Set} (p : ∞Process i A) (p' : ∞Process i B) → Set
Refinement i p p'  = (l : List Label) →  ∞Tr i l p'  → ∞Tr i l p

_⊏_ :  {i : Size} {A B : Set} (p : ∞Process i A) (p' : ∞Process i B) → Set
_⊏_ = Refinement _

Refinement' : (j : Size) {A B : Set} (p : Process j A) (p' : Process j B) → Set
Refinement' j p p'  = (l : List Label) → Tr j l p' → Tr j l p

_⊏'_ :  {j : Size} {A B : Set} (p : Process j A) (p' : Process j B) → Set
_⊏'_ = Refinement' _

-----------------------------------------
mutual
   
    record ∞Trx (i : Size) {A : Set} (l : List Label) (P : ∞Processx  i A) : Set where
     coinductive
     field
       forcex' : (j : Size< i) → Trx j  l (forcex P j)

    data Trx (j : Size) {A : Set} : (l : List Label) -> (P : Processx j A) -> Set where 
        empty : {P : Processx j A} → Trx  j {A} [] P
        extchoice : {P  : Node j A}
         → (x : Node2E P)
         → (l : List Label)
         → ∞Trx j {A} l (node2PE P x)
         → Trx j {A} ((node2Lab P x) :: l) (node P)
        intchoice : {P  : Node j A}
         → (x : Node2I P)
         → (l : Label)
         → (ll : List Label)
         → ∞Trx j {A} (l :: ll) (node2PI P x)
         → Trx  j {A} (l :: ll)  (node P)


open ∞Trx



Refinementx : (i : Size) {A B : Set} (p : ∞Processx i A) (p' : ∞Processx i B) → Set
Refinementx i p p'  = (l : List Label) →  ∞Trx i l p'  → ∞Trx i l p

_⊑_ : {i : Size} {A B : Set} (p : ∞Processx i A) (p' : ∞Processx i B) → Set
_⊑_ = Refinementx _ 


Refinementx' : (j : Size) {A B : Set} (p : Processx j A) (p' : Processx j B) → Set
Refinementx' j p p'  = (l : List Label) → Trx j l p' → Trx j l p

_⊑'_ :  {j : Size} {A B : Set} (p : Processx j A) (p' : Processx j B) → Set
_⊑'_ = Refinementx' _


--------------------------------------------
--------------------------------------------

sym : (i : Size) (j : Size< i) {A B : Set} (p : Process i A) (p' : Process i B) → Set
sym i j p p'  = (l : List Label) → Tr j l p' → Tr j l p

sym' : (i : Size) (j : Size< i) {A B : Set} (p : Process i A) (p' : Process i B) ( l : List Label) (tr : Tr j l p) → Set
sym' i j p p' l tr  =  Tr j l p'

symx : (i : Size) (j : Size< i) {A B : Set} (p : Processx i A) (p' : Processx i B) → Set
symx i j p p'  = (l : List Label) → Trx j l p' → Trx j l p

symx' : (i : Size) (j : Size< i) {A B : Set} (p : ∞Processx i A) (p' : ∞Processx i B) → Set
symx' i j p p'  = (l : List Label) → ∞Trx j l p' → ∞Trx j l p
       
-------------------------------------------------
-------------------------------------------------

reflRef : (i : Size) (A : Set) (P : ∞Process i A) → Refinement i P P 
reflRef i A P  l tr = tr 


reflRef' : (i : Size) (A : Set) (P : Process i A) → Refinement' i P P 
reflRef' i A P  l tr = tr 


reflRefx : (i : Size) (A : Set) (P : ∞Processx i A) → Refinementx i P P 
reflRefx i A P  l tr = tr 

reflRefx' : (i : Size) (A : Set) (P : Processx i A) → Refinementx' i P P 
reflRefx' i A P  l tr = tr 

reflRefx'' : (i : Size) (A B : Set) (P : ∞Processx i A) (P' : ∞Processx i B) → Refinementx i P P' → Set 
reflRefx'' i A B P P' tr  = B    ---Rabish


------------------------------------------------------------
------------------------------------------------------------


SymRef : (i : Size)(A B : Set) (P : ∞Process i A) (Q : ∞Process i B) →((Refinement i P Q) →  (Refinement i Q P)) → (Refinement i P Q) → Refinement i Q P
SymRef i A B P Q f PQ l trP    = f (λ l₁ x₂ → PQ l₁ x₂ ) l trP 


transRef : (i : Size) (A B C : Set) (P : ∞Process i A) (Q : ∞Process i B) (R : ∞Process i C)  → Refinement i P Q  → Refinement i Q R → Refinement i P R 
transRef i A B C P Q R PQ QR l tr  = PQ l (QR l tr)   


transRefx : (i : Size) (A B C : Set) (P : Processx i A) (Q : Processx i B) (R : Processx i C)  → Refinementx' i P Q  → Refinementx' i Q R → Refinementx' i P R 
transRefx i A B C P Q R PQ QR l tr  = PQ l (QR l tr)   

---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

mutual
  indepFmap :  (j : Size) → (A B C : Set) → (f : A → B) → (g : A → C) → (l : List Label) → (P : Processx j A) → 
               Trx j l (fmapx' j f P) →  Trx j l (fmapx' j g P)
 

  indepFmap j A B C f g .[] (node (thenode E Lab PE I PI)) empty = empty
  indepFmap j A B C f g .(Lab x :: l) (node (thenode E Lab PE I PI)) (extchoice x l x₁) =  extchoice x l (indepFmapx j A B C f g l (PE x) x₁)
  indepFmap j A B C f g .(l :: ll) (node (thenode E Lab PE I PI)) (intchoice x l ll x₁) =  intchoice x l ll (indepFmapx j A B C f g (l :: ll) (PI x) x₁)
  indepFmap j A B C f g .[] (terminate x) empty = empty              

  indepFmapx :  (j : Size) → (A B C : Set) → (f : A → B) → (g : A → C) → (l : List Label) → (P : ∞Processx j A) → 
               ∞Trx j l (fmapx j f P) →  ∞Trx j l (fmapx j g P)
  forcex' (indepFmapx j A B C f g l P tr) j'  = indepFmap j' A B C f g l (forcex P j') (forcex' tr j')


------------------------------------------------------------------------------------------------------------------------
-----------------------------------ProofTheProaritesOfreflextyOfExternalChoice------------------------------------------
------------------------------------------------------------------------------------------------------------------------


mutual
 refExtChoice : (i : Size) -> {A B : Set} -> (P : ∞Processx i A) →  (Q : ∞Processx i B) 
            → Refinementx i {(A + B) + (A × B)} {(B + A) + (B × A)} (extChx i P Q) (extChx i Q P) 

 forcex' ( refExtChoice i P Q l x) j  =  refExtChoice' j (forcex P j) (forcex Q j) l (forcex' x j) 

 refExtChoice' : (j : Size) -> {A B : Set} -> (P : Processx j A) →  (Q : Processx j B) 
            → Refinementx' j {(A + B) + (A × B)} {(B + A) + (B × A)} (extChx' j P Q) (extChx' j Q P) 


 refExtChoice' j {A} {B} (node P) (node Q) [] empty = empty
 refExtChoice' j {A} {B} (node P) (node Q) (.(node2Lab Q x) :: l) (extchoice (inl x) .l tr) =  extchoice (inr x) l (refExtChoiceLem1 j A B P Q l x tr)
 refExtChoice' j {A} {B} (node P) (node Q) (.(node2Lab P x) :: l) (extchoice (inr x) .l tr) = extchoice (inl x) l (refExtChoiceLem2 j B A Q P l x tr)
 refExtChoice' j {A} {B} (node P) (node Q) (l₁ :: l) (intchoice (inl x) .l₁ .l x₁) = intchoice (inr x) l₁ l (refExtChoiceLem3 j A B P Q (l₁ :: l) x x₁)
 refExtChoice' j {A} {B} (node P) (node Q) (l₁ :: l) (intchoice (inr x) .l₁ .l x₁) = intchoice (inl x) l₁ l (refExtChoiceLem4 j B A Q P (l₁ :: l) x x₁)
 refExtChoice' j (node P) (terminate Q) [] tr = empty
 refExtChoice' j (node (thenode E Lab PE I PI)) (terminate Q) (x :: x₁) ()
 refExtChoice' j (terminate x) (node x₁) [] empty = empty
 refExtChoice' j (terminate x) (node (thenode E Lab PE I PI)) (x₂ :: x₃) ()
 refExtChoice' j (terminate x) (terminate x₁) .[] empty = empty

 refExtChoiceLem1 : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l  : List Label)
                    → (x  : ChoiceSet (node2E Q))
                    → (tr : ∞Trx j l (extChPE' Q P (inl x))) 
                    → ∞Trx j l (extChPE' P Q (inr x))
 forcex' (refExtChoiceLem1 j A B P Q l x tr) j' = indepFmap j' B  ((B + A) + (B × A)) ((A + B) + (A × B)) (inl ∘ inl) (inl ∘ inr) l (forcex (node2PE Q x) j') (forcex' tr j')
 refExtChoiceLem2xx : (j  : Size)  -> (A  B : Set) → (P  : Processx j A) → (Q  : Processx j B)  → (l  : List Label) 
                    → (tr : Trx j l (extChx' j P Q))
                    →       Trx j l (extChx' j Q P) 
 refExtChoiceLem2xx j A B (node P) (node Q) l tr = refExtChoiceLem2xxx j B A (node Q) (node P) l tr
 refExtChoiceLem2xx j A B (node (thenode E Lab PE I PI)) (terminate x₁) .[] empty = empty
 refExtChoiceLem2xx j A B (terminate x) (node (thenode E Lab PE I PI)) .[] empty = empty
 refExtChoiceLem2xx j A B (terminate x) (terminate x₁) .[] empty = empty

 refExtChoiceLem2xxx : (j  : Size)  -> (A  B : Set) → (P  : Processx j A) → (Q  : Processx j B)
                    → (l  : List Label) 
                    → (tr : Trx j l (extChx' j Q P))
                    →       Trx j l (extChx' j P Q) 

 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .[] empty = empty
 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(Lab₁ x :: l) (extchoice (inl x) l x₁) = extchoice (inr x) l (refExtChoiceLem1 _ _ _ (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁) l x x₁)
 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(Lab x :: l) (extchoice (inr x) l x₁) = extchoice (inl x) l (refExtChoiceLem2 _ _ _ (thenode E₁ Lab₁ PE₁ I₁ PI₁) (thenode E Lab PE I PI) l x x₁)
 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(l :: ll) (intchoice (inl x) l ll x₁) = intchoice (inr x) l ll (refExtChoiceLem3 _ _ _ (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁) (l :: ll) x x₁)
 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(l :: ll) (intchoice (inr x) l ll x₁) = intchoice (inl x) l ll (refExtChoiceLem4 _ _ _ (thenode E₁ Lab₁ PE₁ I₁ PI₁) (thenode E Lab PE I PI) (l :: ll) x x₁) 
 refExtChoiceLem2xxx j A B (node (thenode E Lab PE I PI)) (terminate x₁) .[] empty = empty
 refExtChoiceLem2xxx j A B (terminate x) (node (thenode E Lab PE I PI)) .[] empty = empty
 refExtChoiceLem2xxx j A B (terminate x) (terminate x₁) .[] empty = empty

 refExtChoiceLem2x : (j'  : Size)  -> (j : Size< j') -> (A  B : Set) → (P  : Node j' A) → (Q  : Node j' B) 
                    → (l  : List Label)
                    → (x  : ChoiceSet (node2I Q))
                    → (tr : Trx j l (extChx' j (node P) (forcex (node2PI Q x) j))) -- (forcex (extChPI' P Q (inr x)) j)
                    →       Trx j l (extChx' j (forcex (node2PI Q x) j) (node P))  -- (forcex (extChPI' Q P (inl x)) j)
 refExtChoiceLem2x j j' A B P Q l x tr =  refExtChoiceLem2xx j' A B (node P) (forcex (node2PI Q x) j') l tr

 refExtChoiceLem2x''' : (j'  : Size)  -> (j : Size< j') -> (A  B : Set) → (P  : Node j' A) → (Q  : Node j' B)
                    → (l  : List Label)
                    → (x : ChoiceSet (node2I P))
                    → (tr :  Trx j l (extChx' j (forcex (node2PI P x) j) (node Q))) 
                    →        Trx j l (extChx' j (node Q) (forcex (node2PI P x) j))  
 refExtChoiceLem2x''' j j' A B P Q l x tr = refExtChoiceLem2xxx j' B A (node Q) (forcex (node2PI P x) j') l tr


 refExtChoiceLem2 : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l  : List Label)
                    → (x  : ChoiceSet (node2E Q))
                    → (tr : ∞Trx j l (extChPE' P Q (inr x))) 
                    → ∞Trx j l (extChPE' Q P (inl x))
 forcex' (refExtChoiceLem2 j A B P Q l x tr) j' = indepFmap j' B ((A + B) + (A × B)) ((B + A) + (B × A)) (inl ∘ inr) (inl ∘ inl) l (forcex  (node2PE Q x) j') (forcex' tr j')


 refExtChoiceLem3 : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l : List Label)
                    → (x  : ChoiceSet (node2I Q))
                    → (tr : ∞Trx j l (extChPI' Q P (inl x))) 
                    → ∞Trx j l (extChPI' P Q (inr x))
 forcex' (refExtChoiceLem3 j A B P Q l x tr) j' = refExtChoiceLem2x''' j j' B A Q P l x (forcex' tr j')

 refExtChoiceLem4 : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l : List Label)
                    → (x  : ChoiceSet (node2I Q))
                    → (tr : ∞Trx j l (extChPI' P Q (inr x))) 
                    → ∞Trx j l (extChPI' Q P (inl x))
 forcex' (refExtChoiceLem4 j A B P Q l x tr) j' = refExtChoiceLem2x j j' A B P Q l x (forcex' tr j') 


------------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------------------------
               ------------------------------------------------------------------------------------------------------------------
               ------------------------------------------------------------------------------------------------------------------
               ------------------------------------------------------------------------------------------------------------------


mutual
 ExtChoice'' : (i : Size) -> {A B : Set} -> (P : ∞Processx i A) →  (Q : ∞Processx i B) 
            → (P □ Q) ⊑ (Q □ P) 

 forcex' ( ExtChoice'' i P Q l x) j  =  ExtChoice''' j (forcex P j) (forcex Q j) l (forcex' x j) 

 ExtChoice''' : (j : Size) -> {A B : Set} -> (P : Processx j A) →  (Q : Processx j B) 
            → (P □' Q) ⊑' (Q □' P) 


 ExtChoice''' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .[] empty = empty
 ExtChoice''' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(Lab₁ x :: l) (extchoice (inl x) l x₁) = extchoice (inr x) l (refExtChoiceLem1 j _ _ (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁) l x x₁)
 ExtChoice''' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(Lab x :: l) (extchoice (inr x) l x₁) = extchoice (inl x) l (refExtChoiceLem2 j _ _ (thenode E₁ Lab₁ PE₁ I₁ PI₁) (thenode E Lab PE I PI) l x x₁)
 ExtChoice''' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(l :: ll) (intchoice (inl x) l ll x₁) = intchoice (inr x) l ll (refExtChoiceLem3 j _ _ (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁) (l :: ll) x x₁)
 ExtChoice''' j (node (thenode E Lab PE I PI)) (node (thenode E₁ Lab₁ PE₁ I₁ PI₁)) .(l :: ll) (intchoice (inr x) l ll x₁) = intchoice (inl x) l ll (refExtChoiceLem4 j _ _ (thenode E₁ Lab₁ PE₁ I₁ PI₁) (thenode E Lab PE I PI) (l :: ll) x x₁)
 ExtChoice''' j (node (thenode E Lab PE I PI)) (terminate Q) .[] empty = empty
 ExtChoice''' j (terminate P) (node (thenode E Lab PE I PI)) .[] empty = empty
 ExtChoice''' j (terminate P) (terminate x) .[] empty = empty

-------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------
                          ------------------------------------------------------------------
                          ------------------------------------------------------------------

postulate eqLabel : Label -> Label -> Bool
postulate symEqLabel : (l l' : Label) ->   True (eqLabel l l') ->  True (eqLabel l' l) 
postulate eqLabelIsEq : (l l' : Label) -> True (eqLabel l l') -> l == l'


-------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------
--l ....l₁
--l' ...l₂

mutual
 refParallel : (i : Size) -> {A B : Set} -> (P : ∞Processx i A) →  (Q : ∞Processx i B) 
            → Refinementx i {A × B} {B × A} 
               ( Parallelx i (λ l₁ -> ff) (λ l₂ -> ff) eqLabel (λ l₁ l₂ p -> l₁) A B P Q)
               ( Parallelx i (λ l₂ -> ff) (λ l₁ -> ff) (λ l₁ l₂ → eqLabel l₂ l₁) (λ l₁ l₂ p -> l₂) B A Q P)
 forcex' (refParallel i P Q l x) j  = refParallel' j (forcex P j) (forcex Q j) l (forcex' x j) 

 refParallel' : (j : Size) -> {A B : Set} -> (P : Processx j A) →  (Q : Processx j B) 
            → Refinementx' j {A × B} {B × A} 
               (Parallelx' j (λ l₁ -> ff) (λ l₂ -> ff) eqLabel (λ l₁ l₂ p -> l₁) A B P Q)
               (Parallelx' j (λ l₂ -> ff) (λ l₁ -> ff) (λ l₁ l₂ → eqLabel l₂ l₁) (λ l₁ l₂ p -> l₂) B A Q P)
 refParallel' i (node P) (node Q) .[] empty = empty
 refParallel' i (node P) (node Q) .(node2Lab Q a :: l) (extchoice (inl (inl (sub a ()))) l x₁)
 refParallel' i (node P) (node Q) .(node2Lab P a :: l) (extchoice (inl (inr (sub a ()))) l x₁)
 refParallel' i (node P) (node Q) .(node2Lab P a₁ :: l) (extchoice (inr (sub (a , a₁) x))l x₁) = extchoice (inr (sub (a₁ , a) x)) l {!!}
 refParallel' i {A} {B} (node P) (node Q) .(l :: ll) (intchoice (inl x) l ll x₁) = intchoice (inr x) l ll (Lem i A B P Q (l :: ll)  x x₁)
 refParallel' i {A} {B} (node P) (node Q) .(l :: ll) (intchoice (inr x) l ll x₁) = intchoice (inl x) l ll (Lem₂ i B A Q P (l :: ll) x x₁)
 refParallel' i (node (thenode E Lab PE I PI)) (terminate Q) .[] empty = empty
 refParallel' i (node (thenode E Lab PE I PI)) (terminate Q) .(Lab x :: l) (extchoice x l x₁) = extchoice x l {!!}
 refParallel' i (node (thenode E Lab PE I PI)) (terminate Q) .(l :: ll) (intchoice x l ll x₁) = intchoice x l ll {!!}
 refParallel' i (terminate P) (node (thenode E Lab PE I PI)) .[] empty = empty
 refParallel' i (terminate P) (node (thenode E Lab PE I PI)) .(Lab x :: l) (extchoice x l x₁) = extchoice x l {!!}
 refParallel' i (terminate P) (node (thenode E Lab PE I PI)) .(l :: ll) (intchoice x l ll x₁) = intchoice x l ll {!!}
 refParallel' i (terminate P) (terminate Q) .[] empty = empty 


 Lem : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l : List Label)
                    → (x₁ : ChoiceSet (node2I Q))    
                    → (tr : ∞Trx j l (parPI' (λ l₂ → ff) (λ l₁ → ff) (λ l₁ l₂ → eqLabel l₂ l₁) (λ l₁ l₂ p → l₂) Q P (inl x₁)) )
                    → ∞Trx j l (parPI' (λ l₁ → ff) (λ l₂ → ff) eqLabel (λ l₁ l₂ p → l₁) P Q (inr x₁))
 forcex' (Lem j A B P Q l x₁ tr) j' = refLem j j' B A {!Q!} P l x₁ (forcex' tr j')


 refLem : (j'  : Size)  -> (j : Size< j') -> (A  B : Set) → (P  : Node j' A) → (Q  : Node j' B)
          → (l  : List Label)
          → (x : ChoiceSet (node2I P))
          → (tr :  Trx j l (Parallelx' j (λ l₁ → ff) (λ l₂ → ff) eqLabel (λ l₁ l₂ p → l₁) A B (forcex (node2PI P x) j) (node Q) ))
          → Trx j l (Parallelx' j (λ l' → ff) (λ l₁ → ff) (λ l₁ l' → eqLabel l' l₁) (λ l₁ l' p → l') B A  (node Q) (forcex (node2PI P x) j))        
 refLem j j' A B P Q l x tr = refLemaux j' B A (node Q) (forcex (node2PI {!P!} x) j) l tr


 refLemaux : (j  : Size)  -> (A  B : Set) → (P  : Processx j A) → (Q  : Processx j B)
                    → (l  : List Label) 
                    → (tr : Trx j l (Parallelx' j (λ l₂ → ff) (λ l₁ → ff) (λ l₁ l₂ → eqLabel l₂ l₁) (λ l₁ l₂ p → l₂) B A Q P))   
                    →       Trx j l (Parallelx' j (λ l₁ → ff) (λ l₂ → ff) eqLabel (λ l₁ l₂ p → l₁) A B P Q)  
 refLemaux j A B (node P) (node Q) .[] empty = empty
 refLemaux j A B (node P) (node Q) .(node2Lab Q a :: l) (extchoice (inl (inl (sub a ()))) l x₃)
 refLemaux j A B (node P) (node Q) .(node2Lab P a :: l) (extchoice (inl (inr (sub a ()))) l x₃)
 refLemaux j A B (node P) (node Q) .(node2Lab P a₁ :: l) (extchoice (inr (sub (a , a₁) x)) l x₁) = {!!}
 refLemaux j A B (node P) (node Q) .(l :: ll) (intchoice (inl x) l ll x₁) = intchoice (inr x) l ll (Lem j A B P Q (l :: ll) x x₁)
 refLemaux j A B (node P) (node Q) .(l :: ll) (intchoice (inr x) l ll x₁) = intchoice (inl x) l ll (Lem₂ j B A Q P (l :: ll) x x₁)
 refLemaux j A B (node (thenode E Lab PE I PI)) (terminate Q) .[] empty = {!!}
 refLemaux j A B (node (thenode E Lab PE I PI)) (terminate Q) .(Lab x :: l) (extchoice x l x₁) = {!!}
 refLemaux j A B (node (thenode E Lab PE I PI)) (terminate Q) .(l :: ll) (intchoice x l ll x₁) = {!!}
 refLemaux j A B (terminate P) (node (thenode E Lab PE I PI)) .[] empty = {!!}
 refLemaux j A B (terminate P) (node (thenode E Lab PE I PI)) .(Lab x :: l) (extchoice x l x₁) = {!!}
 refLemaux j A B (terminate P) (node (thenode E Lab PE I PI)) .(l :: ll) (intchoice x l ll x₁) = {!!}
 refLemaux j A B (terminate P) (terminate Q) .[] empty = empty

 Lem₂ : (j  : Size) → (A  B : Set) → (P  : Node j A) → (Q  : Node j B)
                    → (l : List Label)
                    → (x  : ChoiceSet (node2I Q))  
                    → (tr : ∞Trx j l (parPI' (λ l₁ → ff) (λ l₂ → ff) (λ l₁ l₂ → eqLabel l₂ l₁) (λ l₂ l₁ p → l₁) P Q (inr x)) ) 
                    → ∞Trx j l (parPI' (λ l₂ → ff) (λ l₁ → ff) eqLabel (λ l₂ l₁ p → l₂) Q P (inl x))
 forcex' (Lem₂ j A B P Q l x tr) j' = refLem₂ j j' B A Q {!!} l x (forcex' tr j')



 refLem₂ : (j'  : Size)  -> (j : Size< j') -> (A  B : Set) → (P  : Node j' A) → (Q  : Node j' B) 
        → (l  : List Label)
        → (x  : ChoiceSet (node2I Q))
        → (tr : Trx j l (Parallelx' j (λ l₂ → ff) (λ l₁ → ff) (λ l₁ l' → eqLabel l' l₁) (λ l₁ l₂ p → l₂) B A (forcex (node2PI Q x) j) (node P)))
        →   Trx j l (Parallelx' j (λ l₁ → ff) (λ l₂ → ff) eqLabel (λ l₁ l₂ p → l₁) A B (node P) (forcex (node2PI Q x) j))
 refLem₂ j j' A B P Q l x tr = refLemaux₂ j' B A (forcex (node2PI Q x) j') (node P) l tr   
 

 refLemaux₂ : (j  : Size)  -> (A  B : Set) → (P  : Processx j A) → (Q  : Processx j B)
                    → (l  : List Label) 
                    → (tr :  Trx j l (Parallelx' j (λ l₁ → ff) (λ l' → ff) (λ l' l₁ → eqLabel l₁ l') (λ l' l₁ p → l₁) A B P Q))
                    →        Trx j l (Parallelx' j (λ l' → ff) (λ l₁ → ff) eqLabel (λ l' l₁ p → l') B A Q P)
 refLemaux₂ j A B (node P) (node Q) .[] empty = empty
 refLemaux₂ j A B (node P) (node Q) .(node2Lab P a :: l) (extchoice (inl (inl (sub a ()))) l x₁)
 refLemaux₂ j A B (node P) (node Q) .(node2Lab Q a :: l) (extchoice (inl (inr (sub a ()))) l x₁)
 refLemaux₂ j A B (node P) (node Q) .(node2Lab Q x₁ :: l) (extchoice (inr (sub (x , x₁) x₂)) l x₃) = {!!}
 refLemaux₂ j A B (node P) (node Q) .(l :: ll) (intchoice (inl x) l ll x₁) = intchoice (inr x) l ll (Lem j B A Q P (l :: ll) x x₁)
 refLemaux₂ j A B (node P) (node Q) .(l :: ll) (intchoice (inr x) l ll x₁) = intchoice (inl x) l ll (Lem₂ j A B P Q (l :: ll) x x₁)
 refLemaux₂ j A B (node P) (terminate Q) l tr = {!!}
 refLemaux₂ j A B (terminate P) (node Q) l tr = {!!}
 refLemaux₂ j A B (terminate P) (terminate Q) .[] empty = empty




