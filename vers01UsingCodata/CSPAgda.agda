module CSPAgda where

open import Coinduction using (♯_ ; ♭ ; ∞)
open import Data.Nat using (ℕ;suc;zero)
postulate ExtLabel : Set 
postulate tick     : ExtLabel
postulate IntLabel : Set
postulate _==Extl_ : ExtLabel → ExtLabel → Set

data Bool : Set where
  tt ff : Bool

data ⊤ : Set where 
 triv : ⊤ 

data ⊥ : Set where

data ∅ : Set where

data True : Bool → Set  where 
  triv : True tt

Atom : Bool → Set 
Atom tt = ⊤
Atom ff = ⊥

¬_ : Bool → Bool 
¬ tt = ff
¬ ff = tt

data _×_ (A B : Set) : Set where
  _,_  : A -> B -> A × B       -- \times = ×

data _+_ (A B : Set) : Set where
  inl  : A -> A + B 
  inr  : B -> A + B

data List (A : Set ) : Set where
  [] : List A 
  _::_ : A → List A → List A  


data subset (A : Set) (f : A -> Bool) : Set where
  sub : (a : A) -> True (f a) -> subset A f

data Σ (A : Set) (B : A → Set) : Set where
  _,,_  : (a : A) -> B a -> Σ A B      

proj1 : {A : Set} → {f : A → Bool}  → subset A f → A
proj1 (sub a x) = a

mutual
  data ExtChoice : Set where
    ⊤'    : ExtChoice  
    ∅'    : ExtChoice
    Bool' : ExtChoice
    _×'_  : ExtChoice -> ExtChoice -> ExtChoice
    _+'_  : ExtChoice -> ExtChoice -> ExtChoice
    subset' : (E : ExtChoice) -> (ExtChoice2Set E -> Bool) -> ExtChoice

  ExtChoice2Set : ExtChoice → Set 
  ExtChoice2Set ⊤' = ⊤ 
  ExtChoice2Set ∅' = ∅
  ExtChoice2Set Bool' = Bool
  ExtChoice2Set (E ×' F) = ExtChoice2Set E × ExtChoice2Set F
  ExtChoice2Set (E +' F) = ExtChoice2Set E + ExtChoice2Set F
  ExtChoice2Set (subset' E f) = subset (ExtChoice2Set E) f


mutual
  data IntChoice : Set where
    ∅'    : IntChoice
    ⊤'     : IntChoice
    Bool' : IntChoice
    _×'_  : IntChoice -> IntChoice -> IntChoice
    _+'_  : IntChoice -> IntChoice -> IntChoice
    subset' : (E : IntChoice) -> (IntChoice2Set E -> Bool) -> IntChoice
    ExtChoice' : (A : ExtChoice) → IntChoice 
  IntChoice2Set : IntChoice → Set 
  IntChoice2Set ∅' = ∅
  IntChoice2Set ⊤' = ⊤
  IntChoice2Set Bool' = Bool
  IntChoice2Set (E ×' F) = IntChoice2Set E × IntChoice2Set F
  IntChoice2Set (E +' F) = IntChoice2Set E + IntChoice2Set F
  IntChoice2Set (subset' E f) = subset (IntChoice2Set E) f
  IntChoice2Set (ExtChoice' E) = ExtChoice2Set E


----------------------------------------Process5----------------------------------------------------------


data Process5 ( A : Set ) : Set where
 node : (E   : ExtChoice) 
     → (Lab : ExtChoice2Set E → ExtLabel)
     → (PE  : ExtChoice2Set E → ∞ (Process5 A)) 
     → (I   : IntChoice)
     → (PI  : IntChoice2Set I → ∞ (Process5 A))
     → Process5 A
 terminate : A → Process5 A

-----------------------------------------Process5+--------------------------------------------------------

data Process5+ ( A : Set ) : Set where
 node : (E   : ExtChoice) 
     → (Lab : ExtChoice2Set E → ExtLabel)
     → (PE  : ExtChoice2Set E → ∞ (Process5 A)) 
     → (I   : IntChoice)
     → (PI  : IntChoice2Set I → ∞ (Process5 A))
     → Process5+ A


------------------------------------------- Bisim --------------------------------------------------------

data Bisim {A A' : Set} (eq : A → A' → Set) : Process5 A → Process5 A' → Set where
   eqterminate : (a : A) → (a' : A') → eq a a' → Bisim eq (terminate a) (terminate a')
   eqnode   : (E E' : ExtChoice) 
              → (Lab :  ExtChoice2Set E   → ExtLabel)
              → (Lab' : ExtChoice2Set E'  → ExtLabel)
              → (PE   : ExtChoice2Set E   → ∞ (Process5 A)) 
              → (PE'  : ExtChoice2Set E'  → ∞ (Process5 A')) 
              → (I I' : IntChoice)
              → (PI   : IntChoice2Set I   → ∞ (Process5 A))
              → (PI'  : IntChoice2Set I'  → ∞ (Process5 A'))
              → (ee'  : ExtChoice2Set E   → ExtChoice2Set E')
              → (e'e  : ExtChoice2Set E'  → ExtChoice2Set E)
              → (ii'  : IntChoice2Set I   → IntChoice2Set I')
              → (i'i  : IntChoice2Set I'  → IntChoice2Set I)
              → ((e   : ExtChoice2Set E)  → Lab  e  ==Extl Lab' (ee' e ))
              → ((e'  : ExtChoice2Set E') → Lab' e' ==Extl Lab  (e'e e')) 
              → ((e   : ExtChoice2Set E)  → ∞ (Bisim  eq (♭ (PE e))         (♭ (PE' (ee' e)))  ))
              → ((e'  : ExtChoice2Set E') → ∞ (Bisim  eq (♭ (PE  (e'e e'))) (♭ (PE' e'))       ))
              → ((i   : IntChoice2Set I)  → ∞ (Bisim  eq (♭ (PI i))         (♭ (PI' (ii' i)))  ))
              → ((i'  : IntChoice2Set I') → ∞ (Bisim  eq (♭ (PI  (i'i i'))) (♭ (PI' i'))       ))
              → Bisim  eq (node E Lab PE I PI) (node E' Lab' PE' I' PI') 


----------------------------------------- Sequantial Composetion Operation --------------------------------------------

_>>_ : {A : Set} → {B : Set} → Process5 A  → (A → Process5 B) → Process5 B
node E Lab PE I PI >> Y = node E Lab (λ x → ♯ (♭ (PE x) >> Y)) I (λ x → ♯ (♭ (PI x) >> Y))
terminate x        >> Y = Y x   



_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C  
(f ∘ g) a = f ( g a )


π₀ : {A B : Set} -> A × B -> A    
π₀ ( a , b) = a

π₁ : {A B : Set} -> A × B -> B    
π₁ ( a , b) = b


----------------------------------------- Parallel Operation ------------------------------------------------------



ParallelP5' : (isInterLeavedP : ExtLabel → Bool)
         → (isInterLeavedQ : ExtLabel → Bool)
         → (interLeaved    : (PLab : ExtLabel) 
                           → (QLab : ExtLabel)
                           → Bool)  
         → (interLeavedToLabel : (PLab : ExtLabel) 
                           → (QLab : ExtLabel)
                           → True (interLeaved PLab QLab)
                           → ExtLabel)
         → (A B C : Set)
         → (A → B → C)
         → Process5 A
         → Process5 B
         → Process5 C

ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (node E Lab PE I PI) (node E₁ Lab₁ PE₁ I₁ PI₁) 
       = node E₃ Lab' PE' I' PI'
         where
           E' : ExtChoice 
           E' = subset' E (isInterLeavedP ∘ Lab)
           
           E₁' : ExtChoice  
           E₁' = subset' E₁ (isInterLeavedQ ∘ Lab₁)           

           EE₁ : ExtChoice 
           EE₁ = E ×' E₁

           f₁ : ExtChoice2Set EE₁ -> Bool
           f₁ ( e , e₁ ) = interLeaved (Lab e) (Lab₁ e₁)

           EE₁' : ExtChoice
           EE₁' = subset' EE₁ f₁

           E₂ : ExtChoice
           E₂ = E' +' E₁'

           E₃ : ExtChoice
           E₃ = E₂ +' EE₁'

           Lab' : ExtChoice2Set E₃ -> ExtLabel
           Lab' (inl (inl (sub e cond))) = Lab e
           Lab' (inl (inr (sub e₁ cond))) = Lab₁ e₁
           Lab' (inr (sub (e , e₁) cond)) = interLeavedToLabel (Lab e) (Lab₁ e₁) cond

           PE' : ExtChoice2Set E₃ -> ∞ (Process5 C)
           PE' (inl (inl (sub e cond)))  = ♯ (ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (♭ (PE e)) (node E₁ Lab₁ PE₁ I₁ PI₁))
           PE' (inl (inr (sub e₁ cond))) = ♯ ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (node E Lab PE I PI) (♭ (PE₁ e₁))
           PE' (inr (sub (e , e₁) cond)) = ♯ ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (♭ (PE e)) (♭ (PE₁ e₁))
           I' : IntChoice 
           I' = I +' I₁
           PI' :  IntChoice2Set I + IntChoice2Set I₁ → ∞ (Process5 C)
           PI' (inl x) = ♯  ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (♭ (PI x)) (node E₁ Lab₁ PE₁ I₁ PI₁)
           PI' (inr x) = ♯ ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (node E Lab PE I PI) (♭ (PI₁ x))

ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (node E Lab PE I PI) (terminate b) = node E Lab PE' I PI' 
         where 
          PE' :  ExtChoice2Set E → ∞ (Process5 C)
          PE' e  = ♯ ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (♭ (PE e)) (terminate b)

          PI' :  IntChoice2Set I → ∞ (Process5 C)
          PI' i  = ♯ ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (♭ (PI i)) (terminate b)


ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (terminate a) (node E₁ Lab₁ PE₁ I₁ PI₁) = node E₁ Lab₁ PE' I₁ PI'
         where 
          PE' :  ExtChoice2Set E₁ → ∞ (Process5 C)
          PE' e  = ♯ ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (terminate a) (♭ (PE₁ e)) 

          PI' :  IntChoice2Set I₁ → ∞ (Process5 C)
          PI' i  = ♯ ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (terminate a) (♭ (PI₁ i)) 

ParallelP5' isInterLeavedP isInterLeavedQ interLeaved interLeavedToLabel A B C f (terminate a) (terminate b) = terminate (f a b)

----------------------------------------- absurd pattern---------- --------------------------------------------

efq : {A : Set} -> ∅ -> A  
efq ()

----------------------------------------- Internal Choice Operation --------------------------------------------


IntChoice5 : ( A : Set ) → (I : IntChoice) → (PI : IntChoice2Set I → Process5 A) → Process5 A 
IntChoice5 A I PI  = node ∅' efq efq I (λ x → ♯ PI x) 


----------------------------------------- Stop Operation ------------------------------------------------------


STOP : {A : Set} -> A -> Process5 A
STOP a = terminate a 


----------------------------------------- SKIP Operation ------------------------------------------------------


SKIP : {A : Set} -> A -> Process5 A
SKIP a = node ⊤' (λ x → tick) (λ x →  (♯ STOP a)) ∅' efq


----------------------------------------- Renaiming the Termination --------------------------------------------


fmap : {A B : Set} → (A → B) → Process5 A → Process5 B
fmap ab (node E Lab PE I PI) = node E Lab (λ x → ♯ fmap ab (♭ (PE x))) I (λ x → ♯ fmap ab (♭ (PI x)))
fmap ab (terminate x) = terminate (ab x)


------------------------------------------ External Choice Operation -------------------------------------------



ExternalChoice : {A B : Set} → Process5 A → Process5 B  → Process5 ((A + B) + (A × B))
ExternalChoice {A} {B} (node E Lab PE I PI) (node E₁ Lab₁ PE₁ I₁ PI₁) = node EE LLab PEE II PII where
           EE : ExtChoice
           EE = E +' E₁ 
           II : IntChoice
           II = I +' I₁
           LLab : ExtChoice2Set EE → ExtLabel
           LLab (inl x) = Lab x
           LLab (inr x) = Lab₁ x   ---- 3
           PEE :   ExtChoice2Set EE → ∞ (Process5 ((A + B) + (A × B)))
           PEE (inl x) = ♯ fmap (λ x → inl (inl x)) (♭ (PE x))
           PEE (inr x) = ♯ fmap (λ x → inl (inr x) )(♭ (PE₁ x))

           PII :   IntChoice2Set II → ∞ (Process5 ((A + B) + (A × B)))
           PII (inl x) = ♯ ExternalChoice (♭ (PI x)) (node E₁ Lab₁ PE₁ I₁ PI₁)
           PII (inr x) = ♯ ExternalChoice (node E Lab PE I PI) (♭ (PI₁ x))

           
ExternalChoice {A} {B} (node E Lab PE I PI) (terminate b) = node E Lab PE' I PI' where
    PE' : ExtChoice2Set E → ∞ (Process5 ((A + B) + (A × B)))
    PE' e  = ♯ ExternalChoice (♭ (PE e)) (terminate b) 

    PI' : IntChoice2Set I → ∞ (Process5 ((A + B) + (A × B)))
    PI' i = ♯ ExternalChoice (♭ (PI i)) (terminate b)

ExternalChoice {A} {B} (terminate a) (node E Lab PE I PI) = node E Lab PE' I PI' where
    PE' : ExtChoice2Set E → ∞ (Process5 ((A + B) + (A × B)))
    PE' e = ♯ ExternalChoice (terminate a) (♭ (PE e))
    PI'  : IntChoice2Set I → ∞ (Process5 ((A + B) + (A × B)))
    PI' i  = ♯ ExternalChoice (terminate a) (♭ (PI i))  
ExternalChoice (terminate a) (terminate b) = terminate (inr (a , b))


---------------------------------------------- INTERUPET OPERATION -----------------------------------------------



Intrupet : {A B : Set} → Process5 A → Process5 B  → Process5 ((A + B) + (A × B))
Intrupet {A} {B} (node E Lab PE I PI) (node E₁ Lab₁ PE₁ I₁ PI₁) = node EE LLab PEE II PII where
      EE : ExtChoice
      EE = E +' E₁
      LLab : ExtChoice2Set EE → ExtLabel
      LLab (inl x) = Lab x
      LLab (inr x) = Lab₁ x
      II : IntChoice
      II = I +' I₁
      PEE :   ExtChoice2Set EE → ∞ (Process5 ((A + B) + (A × B)))
      PEE (inl x) = ♯ fmap (λ x₁ → inl (inl x₁)) (♭ (PE x))
      PEE (inr x) = ♯ fmap (λ x₁ → inl (inr x₁)) (♭ (PE₁ x))
      PII :  IntChoice2Set II → ∞ (Process5 ((A + B) + (A × B)))
      PII (inl x) = ♯ Intrupet (♭ (PI x)) (node E₁ Lab₁ PE₁ I₁ PI₁)
      PII (inr x) = ♯ Intrupet (node E Lab PE I PI) (♭ (PI₁ x))

Intrupet (node E Lab PE I PI) (terminate b) = terminate (inl (inr b))
Intrupet (terminate a) (node E Lab PE I PI) = terminate (inl (inl a))
Intrupet (terminate a) (terminate b) = terminate (inr (a , b))


----------------------------------------- Renaiming --------------------------------------------

renaiming : {A : Set} → (f : ExtLabel → ExtLabel) → Process5 A  → Process5 A
renaiming f (node E Lab PE I PI) = node E (f ∘ Lab) (λ x → ♯ renaiming f (♭ (PE x))) I (λ x → ♯ renaiming f (♭ (PI x)))
renaiming f (terminate a) = terminate a


----------------------------------------- Hide --------------------------------------------

hidin : {A : Set} → (hide : ExtLabel → Bool) → Process5 A → Process5 A 
hidin hide (node E Lab PE I PI) = node (subset' E (λ x → ¬ hide (Lab x))) (λ x → Lab (proj1 x)) (λ x → ♯ hidin hide (♭ (PE (proj1 x)))) (I +' ExtChoice' (subset' E (λ x → hide (Lab x)))) (λ x → ♯ hidin hide  (♭ ( PII x )))
 where
  PII : IntChoice2Set (I +' ExtChoice' (subset' E (λ x → hide (Lab x)))) →
          ∞ (Process5 _)
  PII (inl x) = PI x
  PII (inr x) = PE (proj1 x)

hidin hide (terminate x) = terminate x


-------------------------------------------rec--------------------------------------------------

rec' : {A B : Set} →  (A -> Process5 (A + B)) →  Process5 (A + B) → Process5 B
rec' f (node E Lab PE I PI) = node E Lab (λ x → ♯ rec' f (♭ (PE x))) I (λ x → ♯ rec' f (♭ (PI x)))
rec' f (terminate (inl a)) = node ∅' (λ ()) (λ ()) ⊤' (λ x → ♯ rec' f (f a))
rec' f (terminate (inr b)) = terminate b


-------------------------------------------------------------------------------------------------

data Tr (A : Set) : List ExtLabel → Process5 A → Set where 
 empty : (p : Process5 A) → Tr A [] p
 extchoice : (E   : ExtChoice) 
     → (Lab : ExtChoice2Set E → ExtLabel)
     → (PE  : ExtChoice2Set E → ∞ (Process5 A)) 
     → (I   : IntChoice)
     → (PI  : IntChoice2Set I → ∞ (Process5 A))
     → (x : ExtChoice2Set E)
     → (l : List ExtLabel)
     → Tr A l (♭ (PE x))
     → Tr A ((Lab x) :: l) (node E Lab PE I PI) 
 intchoice : (E   : ExtChoice) 
     → (Lab : ExtChoice2Set E → ExtLabel)
     → (PE  : ExtChoice2Set E → ∞ (Process5 A)) 
     → (I   : IntChoice)
     → (PI  : IntChoice2Set I → ∞ (Process5 A))
     → (x : IntChoice2Set I)
     → (l : List ExtLabel)
     → ∞ (Tr A l (♭ (PI x)))
     → Tr A l (node E Lab PE I PI) 


Refinement : (A : Set) (p p' : Process5 A) → Set
Refinement A p p' = (l : List ExtLabel) →  Tr A l p' → Tr A l p


