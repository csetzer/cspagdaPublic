module ProcessInTypeC where 

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
E   (P ||| Q )        = E P +' E Q
Lab (P ||| Q) (inl x) = Lab P x
Lab (P ||| Q) (inr x) = Lab Q x
PE  (P ||| Q) (inl x) = PE P x  ||| Q
PE  (P ||| Q) (inr x) = P       ||| PE Q x
I   (P ||| Q )        = I P +' I Q
PI  (P ||| Q) (inl x) = PI P x  ||| Q
PI  (P ||| Q) (inr x) = P       ||| PI Q x


_□_ : Process → Process → Process
E (P □ Q )          = E P +' E Q
Lab (P □ Q) (inl c) = Lab P c
Lab (P □ Q) (inr c) = Lab Q c
PE (P □ Q)  (inl c) = PE P c
PE (P □ Q)  (inr c) = PE Q c
I (P □ Q )          = I P +' I Q
PI (P □ Q) (inl c)  = PI P c  □ Q
PI (P □ Q) (inr c)  = P       □ PI Q c

{-
  extChPI'toP : (P : Process) → (Q : Process)  
                → ChoiceSet (I P) + ChoiceSet (I Q) →  ∞Process 
  extChPI'toP P Q (inl x) = PI P x
  extChPI'toP P Q (inr x) = P
-}

record  SizedProcess (i : Size) : Set where
  coinductive
  field
    E'   : Choice
    Lab' : ChoiceSet E' → Label
    PE'  : (j : Size< i) → ChoiceSet E' → SizedProcess j
    I'   : Choice
    PI'  : (j : Size< i) → ChoiceSet I' → SizedProcess j

open SizedProcess

record  ∞SizedProcess (i : Size) : Set where
  coinductive
  constructor
    delay
  field
    force : (j : Size< i) → SizedProcess j

open ∞SizedProcess




_|||'_ : ∀ {i} →  SizedProcess i → SizedProcess i → SizedProcess i
E'   (P |||' Q )          = E' P +' E' Q
Lab' (P |||' Q) (inl x)   = Lab' P x
Lab' (P |||' Q) (inr x)   = Lab' Q x
PE'  (P |||' Q) j (inl x) = PE' P j x  |||'  Q
PE'  (P |||' Q) j (inr x) = P          |||' PE' Q j x
I'   (P |||' Q)           = I' P +' I' Q
PI'  (P |||' Q) j (inl x) = PI' P j x  |||' Q
PI'  (P |||' Q) j (inr x) = P          |||' PI' Q j x




mutual
   
    data Tr {i : Size}  : (l : List Label) → (P : SizedProcess i) → Set where 
        empty : {P : SizedProcess i} → Tr [] P
        trE : {j : Size< i} 
         → {P  : SizedProcess i}
         → (x : ChoiceSet (E' {i} P))
         → (l : List Label)
         → Tr l (PE' P j x)
         → Tr (Lab' {i} P x :: l) P
        trI : {j : Size< i} 
         → {P  : SizedProcess i}
         → (x : ChoiceSet (I' {i} P))
         → (l : List Label)
         → Tr l (PI' P j x)
         → Tr l  P



_⊑_    : {i : Size} (P : SizedProcess i) (P' : SizedProcess i) → Set
P ⊑ P' = (l : List Label) →  Tr l P'  → Tr l P



infixl 5 _⊑_  


sym|||  :{i : Size} 
         → (P Q : SizedProcess i) 
         → (P |||' Q) ⊑  (Q |||' P)
sym||| P Q .[] empty = empty
sym||| P Q ._ (trE {j} (inl x) l tr) = trE (inr x) l (sym||| P (PE' Q j x) l tr)
sym||| P Q ._ (trE {j} (inr x) l tr) = trE (inl x) l (sym||| (PE' P j x) Q l tr)
sym||| P Q ._ (trI {j} (inl x) l tr) = trI (inr x) l (sym||| P (PI' Q j x) l tr)
sym||| P Q ._ (trI {j} (inr x) l tr) = trI (inl x) l (sym||| (PI' P j x) Q l tr)





mutual 

  _comp_ : {i : Size} → {j : Size< (↑ i)} → (P : SizedProcess j) → (Q : SizedProcess i ) → SizedProcess j
  P comp Q = compaux (E' P) (Lab' P) (PE' P) (I' P) (PI' P) Q

  compaux : {i : Size} → {j : Size< (↑ i)}
                       → (E : Choice) → (Lab : ChoiceSet E → Label) 
                       → (PE  : (j' : Size< j) → ChoiceSet E → SizedProcess j')
                       → (I   : Choice)
                       → (PI  : (j' : Size< j) → ChoiceSet I → SizedProcess j')
                       → (Q : SizedProcess i ) → SizedProcess j 
  compaux ∅' Lab PE ∅' PI Q = Q
  compaux E Lab PE I PI Q = compaux' E Lab PE I PI Q  


  compaux' : {i : Size} → {j : Size< (↑ i)}
                        → (E : Choice) → (Lab : ChoiceSet E → Label) 
                        → (PE  : (j' : Size< j) → ChoiceSet E → SizedProcess j')
                       → (I   : Choice)
                       → (PI  : (j' : Size< j) → ChoiceSet I → SizedProcess j')
                       → (Q : SizedProcess i ) → SizedProcess j 
  E' (compaux' E Lab PE I PI Q) = E
  Lab' (compaux' E Lab PE I PI Q) c = Lab c
  PE' (compaux' E Lab PE I PI Q) j' c = (PE j' c) comp Q
  I'  (compaux' E Lab PE I PI Q) = I
  PI' (compaux' E Lab PE I PI Q) j c = (PI j c) comp Q


_∞comp_ : {i : Size} → {j : Size< (↑ i)} → (P : ∞SizedProcess j) → (Q : SizedProcess i ) → ∞SizedProcess j
force (P ∞comp Q) j  = (force P j) comp Q

∞loop : (i : Size) → (P : ∞SizedProcess i) → ∞SizedProcess i
force (∞loop i P) j = force P j  comp force P j

loop : (i : Size) → (P : SizedProcess i) → SizedProcess i
loop i P = force (∞loop (↑ i) P''  ) i  where
    P'' : ∞SizedProcess (↑ i)
    force P'' j = P


{-
loop : (i : Size) → (P : SizedProcess i) → SizedProcess i
E' (loop i P) = E' (P comp (loop i P))
Lab' (loop i P) = Lab' (P comp (loop i P))
PE' (loop i P) = PE' (P comp (loop i P))
I' (loop i P) = I' (P comp (loop i P))
PI' (loop i P) = PI' (P comp (loop i P))
-}


{-
mutual 
  _comp_ : {i : Size} → (P : SizedProcess i) → (Q : SizedProcess ∞ ) → SizedProcess i
  P comp Q = compaux (E' P) (Lab' P) (PE' P) (I' P) (PI' P) Q

  compaux : {i : Size} → (E : Choice) → (Lab : ChoiceSet E → Label) 
                       → (PE  : (j : Size< i) → ChoiceSet E → SizedProcess j)
                       → (I   : Choice)
                       → (PI  : (j : Size< i) → ChoiceSet I → SizedProcess j)
                       → (Q : SizedProcess ∞ ) → SizedProcess i 
  compaux ∅' Lab PE ∅' PI Q = Q
  compaux {i} E Lab PE I PI Q = record { E' = E; Lab' = Lab; PE' = PE''; I' = I; PI' = PI} where
           PE'' : (j : Size< i) → ChoiceSet E → SizedProcess j
           PE'' j e = _comp_ (PE j e ) Q

--  E' (compaux E Lab PE I PI Q) = E
--  Lab' (compaux E Lab PE I PI Q) c  = {!!} -- Lab' record { E' = E ; Lab' = Lab ; PE' = PE ; I' = I ; PI' = PI} {!!}
--  PE' (compaux E Lab PE I PI Q) j c = record { E' = E ; Lab' = Lab ; PE' = PE ; I' = I ; PI' = PI} comp Q  
--  I'  (compaux E Lab PE I PI Q) = I
--  PI' (compaux E Lab PE I PI Q) j c = record { E' = E ; Lab' = Lab ; PE' = PE ; I' = I ; PI' = PI} comp Q



loop : (i : Size) → (P : SizedProcess i) → SizedProcess i
loop i P = {!!}
-}



mutual 
  record  ∞SizedProcess' (i : Size) : Set where
    coinductive
    constructor
      delay
    field
      force' : (j : Size< i) → SizedProcess' i

  record  SizedProcess' (i : Size) : Set where
    coinductive
    field
      E''   : Choice
      Lab'' : ChoiceSet E'' → Label
      PE''  : ChoiceSet E'' → ∞SizedProcess' i
      I''   : Choice
      PI''  : ChoiceSet I'' → ∞SizedProcess' i

open SizedProcess'
open ∞SizedProcess'

Not∅ : Choice → Set
Not∅ ∅' = ⊥
Not∅ E  = ⊤ 

NotSTOP : {i : Size} → SizedProcess' i → Set
NotSTOP P = Not∅ (E'' P) ∨ Not∅ (I'' P)  

NotSTOP∞  : {i : Size} → ∞SizedProcess' i → Set
NotSTOP∞ {i}  P = (j : Size< i) → NotSTOP {j} (force' P j)



mutual 

  comp∞'' : {i : Size} → {j : Size< (↑ i)} 
            → (P : ∞SizedProcess' j) 
            → NotSTOP∞ P
            → (Q : ∞SizedProcess' i ) 
            → ∞SizedProcess' j
  force' (comp∞'' {i} {j} P pP Q ) j' = {!!} 

  _comp∞'_ : {i : Size} → {j : Size< (↑ i)} 
             → (P : ∞SizedProcess' j) 
             → (Q : SizedProcess' i ) 
             → ∞SizedProcess' j
  force' (_comp∞'_ {i} {j} P  Q) j' = (force' P j') comp' Q

  _comp'_ : {i : Size} → {j : Size< (↑ i)} 
            → (P : SizedProcess' j) 
            → (Q : SizedProcess' i ) 
            → SizedProcess' j
  _comp'_ {i} {j} P  Q = compaux'' {i} {j} (E'' P) (Lab'' P) (PE'' P) (I'' P) (PI'' P) Q

  compaux'' : {i : Size} → {j : Size< (↑ i)}
                       → (E : Choice) → (Lab : ChoiceSet E → Label) 
                       → (PE  : ChoiceSet E → ∞SizedProcess' j)
                       → (I   : Choice)
                       → (PI  : ChoiceSet I → ∞SizedProcess' j)
                       → (Q : SizedProcess' i ) → SizedProcess' j 
  compaux'' ∅' Lab PE ∅' PI Q = Q
  compaux'' E Lab PE I PI Q = compaux''' E Lab PE I PI Q  


  compaux''' : {i : Size} → {j : Size< (↑ i)}
                        → (E : Choice) → (Lab : ChoiceSet E → Label) 
                        → (PE  : ChoiceSet E → ∞SizedProcess' j)
                       → (I   : Choice)
                       → (PI  : ChoiceSet I → ∞SizedProcess' j)
                       → (Q : SizedProcess' i ) → SizedProcess' j 
  E'' (compaux''' E Lab PE I PI Q) = E
  Lab'' (compaux''' E Lab PE I PI Q) c = Lab c
  PE'' (compaux''' E Lab PE I PI Q) c = (PE c) comp∞' Q
  I''  (compaux''' E Lab PE I PI Q) = I
  PI'' (compaux''' E Lab PE I PI Q) c = (PI c) comp∞' Q


{-
mutual 
  ∞loop' : (i : Size) → (P : ∞SizedProcess' i) → ∞SizedProcess' i
  force' (∞loop' i P) j  = force' P j comp' force' (∞loop' i P) j 
-}


∞loop' : (i : Size) → (P : ∞SizedProcess' i) → NotSTOP∞ P → ∞SizedProcess' i
∞loop' i P = {!!}



mutual 
  record  ∞MProcess (A : Set) (i : Size) : Set where
    coinductive
    constructor
      delay
    field
      forcem : (j : Size< i) → MProcess A j

  data MProcess (A : Set) : (i : Size)  → Set where
    terminate : ∀ {i} → A → MProcess A i
    node      : ∀ {i} → Node A i → MProcess A i


  record  Node (A : Set) (i : Size) : Set where
    coinductive
    field
      Em   : Choice
      Labm : ChoiceSet Em → Label
      PEm  : ChoiceSet Em →  ∞MProcess A i
      Im   : Choice
      PIm  : ChoiceSet Im → ∞MProcess A i



open MProcess
open ∞MProcess
open Node

mutual
  fmap∞  : {A B : Set} → (f : A → B) → (i : Size) → ∞MProcess A i  → ∞MProcess B i  
  forcem (fmap∞  {A} {B} f i P) j = fmap f j (forcem P j)

  fmap  : {A B : Set} → (f : A → B) → (i : Size) → MProcess A i  → MProcess B i  
  fmap f i (terminate a) = terminate (f a)
  fmap f i (node P) = node (fmapn f i P)

  fmapn  : {A B : Set} → (f : A → B) → (i : Size) → Node A i  → Node B i  
  Em   (fmapn  {A} {B} f i P)   = Em P
  Labm (fmapn  {A} {B} f i P) c = Labm P c
  PEm  (fmapn  {A} {B} f i P) c = fmap∞ f i (PEm P c)
  Im   (fmapn  {A} {B} f i P)   = Im P
  PIm  (fmapn  {A} {B} f i P) c = fmap∞ f i (PIm P c)





mutual
  _|||m∞∞_ : {A B  : Set} → {i : Size} → ∞MProcess A i → ∞MProcess B i → ∞MProcess (A × B) i
  forcem (P |||m∞∞  P') i = forcem P i |||m forcem P' i 


  _|||m∞n_ : {A B : Set} → {i : Size} → ∞MProcess A i → Node B i → ∞MProcess (A × B) i
  forcem (P |||m∞n  P') i = forcem P i |||mpn P'

  _|||mn∞_ : {A : Set} → {B : Set} → {i : Size} → Node A i → ∞MProcess B i → ∞MProcess (A × B) i
  forcem (P |||mn∞  P') i = P |||mnp forcem P' i

  _|||m_ : {A B : Set} → {i : Size} → MProcess A i → MProcess B i → MProcess (A × B) i
  _|||m_ {A} {B} {i} (terminate a)  P' = fmap (λ b → a , b) i P'
  node P      |||m P' = P |||mnp P'

  _|||mnp_ : {A B : Set} → {i : Size} → Node A i → MProcess B i → MProcess (A × B) i
  _|||mnp_ {A} {B} {i} P (terminate b) = node (fmapn (λ a → (a , b)) i P)
  P |||mnp node P' = node (P |||mn P')

  _|||mpn_ : {A B : Set} → {i : Size} → MProcess A i → Node B i → MProcess (A × B) i
  _|||mpn_ {A} {B} {i} (terminate a)  P' = node (fmapn (λ b → (a , b)) i P')
  node P |||mpn P' = node (P |||mn P')


  _|||mn_ : {A B : Set} → {i : Size} → Node A i → Node B i → Node (A × B) i
  Em   (P |||mn Q )        = Em P +' Em Q
  Labm (P |||mn Q) (inl x) = Labm P x
  Labm (P |||mn Q) (inr x) = Labm Q x
  PEm  (P |||mn Q) (inl x) = PEm P x  |||m∞n   Q
  PEm  (P |||mn Q) (inr x) = P       |||mn∞  PEm Q x
  Im   (P |||mn Q )        = Im P +' Im Q
  PIm  (P |||mn Q) (inl x) = PIm P x  |||m∞n Q
  PIm  (P |||mn Q) (inr x) = P       |||mn∞ PIm Q x








mutual
  _□m∞∞_ : {A B  : Set} → {i : Size} → ∞MProcess A i → ∞MProcess B i → ∞MProcess ((A + B) + (A × B)) i
  forcem (P □m∞∞  P') i = forcem P i □m forcem P' i 


  _□m∞n_ : {A B : Set} → {i : Size} → ∞MProcess A i → Node B i → ∞MProcess ((A + B) + (A × B)) i
  forcem (P □m∞n  P') i = forcem P i □mpn P'

  _□mn∞_ : {A : Set} → {B : Set} → {i : Size} → Node A i → ∞MProcess B i → ∞MProcess ((A + B) + (A × B)) i
  forcem (P □mn∞  P') i = P □mnp forcem P' i

  _□m_ : {A B : Set} → {i : Size} → MProcess A i → MProcess B i → MProcess ((A + B) + (A × B)) i
  _□m_ {A} {B} {i} (terminate a)  P' = {!!}  --fmap (λ b → a , b) i P'
  node P      □m P' = P □mnp P'

  _□mnp_ : {A B : Set} → {i : Size} → Node A i → MProcess B i → MProcess ((A + B) + (A × B)) i
  _□mnp_ {A} {B} {i} P (terminate b) = {!!} -- node (fmapn (λ a → (a , b)) i P)
  P □mnp node P' = node (P □mn P')

  _□mpn_ : {A B : Set} → {i : Size} → MProcess A i → Node B i → MProcess ((A + B) + (A × B)) i
  _□mpn_ {A} {B} {i} (terminate a)  P' = {!!} -- node (fmapn (λ b → (a , b)) i P')
  node P □mpn P' = node (P □mn P')


  _□mn_ : {A B : Set} → {i : Size} → Node A i → Node B i → Node ((A + B) + (A × B)) i
  Em   (P □mn Q )        =  Em P +' Em Q
  Labm (P □mn Q) (inl x) = Labm P x
  Labm (P □mn Q) (inr x) = Labm Q x
  PEm  (P □mn Q) (inl x) = {!!} --PEm P x
  PEm  (P □mn Q) (inr x) =  {!!} --PEm Q x
  Im   (P □mn Q )        = Im P +' Im Q
  PIm  (P □mn Q) (inl x) = {!!} --PIm P x
  PIm  (P □mn Q) (inr x) = {!!} --PIm Q x


