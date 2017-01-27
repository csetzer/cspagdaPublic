module interleave where 

open import Size
open import process
open ∞Process
open import choiceSetU
open import choiceAuxFunction
open import dataAuxFunction
open import auxData
open import label
open import Data.String renaming (_++_ to _++s_)
open import showFunction



mutual
   Interleave : (i : Size)
          → (c₀ c₁ : Choice)
          → ∞Process i (ChoiceSet c₀)
          → ∞Process i (ChoiceSet c₁)
          → ∞Process i ((ChoiceSet c₀) × (ChoiceSet c₁))

   force (Interleave i  c₀ c₁ P Q) j = Interleave' j  c₀ c₁ (force P j) (force Q j)  

   Interleave' : (i : Size)
          → (c₀ c₁ : Choice)
          → Process i (ChoiceSet c₀)
          → Process i (ChoiceSet c₁)
          → Process i ((ChoiceSet c₀) × (ChoiceSet c₁))


   Interleave' i c₀ c₁ (node E Lab PE I PI Stat) (node E₁ Lab₁ PE₁ I₁ PI₁ Stat₁) = node E' Lab' PE' I' PI' (Stat ++s "|||" ++s Stat₁)
         where
           E' : Choice 
           E' =  E +'' E₁ 
              
           Lab' : ChoiceSet E' →  Label
           Lab' (inl x) = Lab x
           Lab' (inr x) = Lab₁ x
                               
           PE' : ChoiceSet E' → ∞Process i ((ChoiceSet c₀) × (ChoiceSet c₁))                                                         
           force (PE' (inl x)) j = Interleave' j c₀ c₁ ((force (PE x) j)) ((node E₁ Lab₁ PE₁ I₁ PI₁ Stat₁))
           force (PE' (inr x)) j = Interleave' j c₀ c₁ ((node E Lab PE I PI Stat)) ((force (PE₁ x) j))
         
           I' : Choice 
           I' = I +'' I₁

           PI' : ChoiceSet I' → ∞Process i ((ChoiceSet c₀) × (ChoiceSet c₁))
           force (PI' (inl x)) j = Interleave' j c₀ c₁ (force (PI x) j) (node E₁ Lab₁ PE₁ I₁ PI₁ Stat₁)
           force (PI' (inr x)) j = Interleave' j c₀ c₁ (node E Lab PE I PI Stat) (force (PI₁ x) j)

   Interleave' i c₀ c₁ (node E Lab PE I PI Stat) (terminate Q) = node E Lab PE' I PI' (((Stat ++s "|||" ++s showProcess c₁ (terminate Q))))
       where
         PE' : ChoiceSet E → ∞Process i ((ChoiceSet c₀) × (ChoiceSet c₁))
         force (PE' e) j = Interleave' j c₀ c₁ (force (PE e) j) (terminate Q) 
        
         PI' : ChoiceSet I → ∞Process i ((ChoiceSet c₀) × (ChoiceSet c₁))
         force (PI' i') j = Interleave' j c₀ c₁ (force (PI i') j) (terminate Q)

   Interleave' i c₀ c₁ (terminate P) (node E Lab PE I PI Stat) = node E Lab PE' I PI' ((showProcess c₀ (terminate P) ++s "|||" ++s Stat))
       where
        PE' : ChoiceSet E → ∞Process i ((ChoiceSet c₀) × (ChoiceSet c₁)) 
        force (PE' e) j = Interleave' j c₀ c₁ (terminate P) (force (PE e) j)

        PI' : ChoiceSet I → ∞Process i ((ChoiceSet c₀) × (ChoiceSet c₁))
        force (PI' i') j = Interleave' j c₀ c₁ (terminate P) (force (PI i') j) 
   Interleave' i c₀ c₁ (terminate P) (terminate Q) =  terminate (P , Q)

_|||∞_ : {i : Size}         
          → {c₀ c₁ : Choice}
          → ∞Process i (ChoiceSet c₀)
          → ∞Process i (ChoiceSet c₁)
          → ∞Process i ((ChoiceSet c₀) × (ChoiceSet c₁))
 
_|||∞_ {i} {c₀} {c₁}  = Interleave i c₀ c₁



_|||_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process i (ChoiceSet c₀)
          → Process i (ChoiceSet c₁)
          → Process i ((ChoiceSet c₀) × (ChoiceSet c₁))
 
_|||_ {i} {c₀} {c₁}   = Interleave' i c₀ c₁


infixl 10 _|||∞_  
infixl 10 _|||_  


