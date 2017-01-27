module CSPAgdaUnused where

open import Coinduction using (♯_ ; ♭ ; ∞)
open import Data.Nat using (ℕ;suc;zero)
open import CSPAgda

--------------------- Labels will be postulated here ---------------------
--------------------- they could as well be taken as a parameter ---------

postulate tick     : Label
postulate IntLabel : Set

-- We postulate an equality on Label

postulate _==Extlb_ : Label → Label → Bool

_==Extl_ : Label → Label → Set
l ==Extl l' = True (l ==Extlb  l')




-------------------  Recursion where the loop might terminate immediately    ------
-------------------- to take core of this there is a tau transition in
-------------------- case of termination to the next iteration 

mutual
  rec'  : {A B : Set}
         → (A → Process (A + B))
         → A → Process B
  rec' P a = rec'' (P a) P
  
  rec'' : {A B : Set} 
         →  Process (A + B) 
         →  (A →  Process (A + B)) 
         → Process B
  rec'' (node E Lab PE I PI) f 
          = node E Lab 
                 (λ x → ♯ rec''  (♭ (PE x)) f) 
                 I 
                 (λ x → ♯ rec''  (♭ (PI x)) f)
  rec'' (terminate (inl a)) f = node ∅' efq efq ⊤' (λ x → ♯ rec'' (f a) f)
  rec'' (terminate (inr b)) f = terminate b

--------------------------- Indexed External Choice ------------------

process2E : {A : Set} → Process A → Choice
process2E (node E Lab PE I PI) = E
process2E (terminate _)        = ∅'

process2Lab : {A : Set} → (P : Process A) → ChoiceSet (process2E P) → Label
process2Lab (node E Lab PE I PI) = Lab
process2Lab (terminate _)        = efq


process2PE : {A : Set} → (P : Process A) → ChoiceSet (process2E P) 
             → ∞ (Process A)
process2PE (node E Lab PE I PI)  = PE
process2PE (terminate _)         = efq

process2I : {A : Set} → Process A → Choice
process2I (node E Lab PE I PI) = I
process2I (terminate _)        = ∅'

process2PI : {A : Set} → (P : Process A) → ChoiceSet (process2I P) 
             → ∞ (Process A)
process2PI (node E Lab PE I PI)  = PI
process2PI (terminate _)         = efq


-- process2Termchoice gives all the possibilities for termination

process2TermChoice : {A : Set} → Process A → Choice
process2TermChoice (node E Lab PE I PI)  = ∅'
process2TermChoice (terminate _)         = ⊤'

process2TermResult : {A : Set} → (P : Process A) 
                     → ChoiceSet (process2TermChoice P)
                     → A                            
process2TermResult (node E Lab PE I PI)  ()
process2TermResult (terminate a)         triv = a




IndexedExternalChoice : (J : Choice) 
                → (eqJ : (j j' : ChoiceSet J) → (j == j') ∨  (¬ (j == j')))
                → (A : ChoiceSet J → Set)
                → (P : (j : ChoiceSet J) → Process (A j))
                → Process (Σ (ChoiceSet J) A)
IndexedExternalChoice J eqJ A P 
     = node E Lab PE I PI   where

       E : Choice
       E = Σ' J (λ j → process2E (P j))
  
       Lab : ChoiceSet E → Label
       Lab (j ,, e) = process2Lab (P j) e

       PE : ChoiceSet E → ∞ (Process (Σ (ChoiceSet J) A))
       PE (j ,, e) = ♯  (fmap (λ a → (j ,, a))  (♭ (process2PE (P j) e)))

       -- Iτ are the choices for a process making a tau transition
       Iτ : Choice
       Iτ = Σ' J (λ j → process2I (P j))
 
       -- PIτaux  is the new collection of processes indexed over ChoiceSet J
       -- which is in case of j = j' the new process, and otherwise
       -- the original one

       PIτaux : ChoiceSet Iτ  → (j : ChoiceSet J) → ∞ (Process (A j))
       PIτaux (j ,, i) j' with eqJ j j'
       ... | (inl jj') = transfer  (λ j' → ∞ (Process (A j'))) j j' jj' 
                                   (process2PI (P j) i)
       ... | (inr _) = ♯ P j'

       PIτ : ChoiceSet Iτ  → ∞ (Process (Σ (ChoiceSet J) A))
       PIτ  x  =  ♯ IndexedExternalChoice J eqJ A  (λ j → ♭ (PIτaux x j))
      

       -- Iterm  are the choices for a process to terminate

       Iterm : Choice
       Iterm = Σ' J (λ j → process2TermChoice (P j))

       PIterm : ChoiceSet Iterm  → ∞ (Process (Σ (ChoiceSet J) A))
       PIterm (j ,, i) = ♯  (terminate (j ,, process2TermResult (P j) i))

       I : Choice
       I = Iτ  +' Iterm
     
       PI : ChoiceSet I → ∞ (Process (Σ (ChoiceSet J) A))
       PI (inl i) = PIτ i
       PI (inr i) = PIterm i




--------------------------------------- Bisimulation --------------------------------------------------------

data Bisim {A A' : Set} (eq : A → A' → Set) 
           : Process A → Process A' → Set where
   eqterminate : (a : A) → (a' : A') → eq a a' 
                 → Bisim eq (terminate a) (terminate a')
   eqnode   : (E E' : Choice) 
              → (Lab :  ChoiceSet E   → Label)
              → (Lab' : ChoiceSet E'  → Label)
              → (PE   : ChoiceSet E   → ∞ (Process A)) 
              → (PE'  : ChoiceSet E'  → ∞ (Process A')) 
              → (I I' : Choice)
              → (PI   : ChoiceSet I   → ∞ (Process A))
              → (PI'  : ChoiceSet I'  → ∞ (Process A'))
              → (ee'  : ChoiceSet E   → ChoiceSet E')
              → (e'e  : ChoiceSet E'  → ChoiceSet E)
              → (ii'  : ChoiceSet I   → ChoiceSet I')
              → (i'i  : ChoiceSet I'  → ChoiceSet I)
              → ((e   : ChoiceSet E)  → Lab  e  ==Extl Lab' (ee' e ))
              → ((e'  : ChoiceSet E') → Lab' e' ==Extl Lab  (e'e e')) 
              → ((e   : ChoiceSet E)  
                 → ∞ (Bisim  eq (♭ (PE e))         (♭ (PE' (ee' e)))  ))
              → ((e'  : ChoiceSet E') 
                 → ∞ (Bisim  eq (♭ (PE  (e'e e'))) (♭ (PE' e'))       ))
              → ((i   : ChoiceSet I)  
                 → ∞ (Bisim  eq (♭ (PI i))         (♭ (PI' (ii' i)))  ))
              → ((i'  : ChoiceSet I')    
                 → ∞ (Bisim  eq (♭ (PI  (i'i i'))) (♭ (PI' i'))       ))
              → Bisim  eq (node E Lab PE I PI) (node E' Lab' PE' I' PI') 





-------------------- Traces     ------------------------------------------------------

data Tr (A : Set) : List Label → Process A → Set where 
 empty : (p : Process A) → Tr A [] p
 extchoice : (E   : Choice) 
     → (Lab : ChoiceSet E → Label)
     → (PE  : ChoiceSet E → ∞ (Process A)) 
     → (I   : Choice)
     → (PI  : ChoiceSet I → ∞ (Process A))
     → (x : ChoiceSet E)
     → (l : List Label)
     → Tr A l (♭ (PE x))
     → Tr A ((Lab x) :: l) (node E Lab PE I PI) 
 intchoice : (E   : Choice) 
     → (Lab : ChoiceSet E → Label)
     → (PE  : ChoiceSet E → ∞ (Process A)) 
     → (I   : Choice)
     → (PI  : ChoiceSet I → ∞ (Process A))
     → (x : ChoiceSet I)
     → (l : List Label)
     → ∞ (Tr A l (♭ (PI x)))
     → Tr A l (node E Lab PE I PI) 


Refinement : (A : Set) (p p' : Process A) → Set
Refinement A p p' = (l : List Label) →  Tr A l p' → Tr A l p


