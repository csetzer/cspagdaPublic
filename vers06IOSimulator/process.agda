module process where 

open import choiceSetU
open import label
open import Size
open import Data.String



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
           → (Stat : String )
           → Process i A
       terminate : A → Process i A

open ∞Process

data Process+ (i : Size) ( A : Set ) : Set where
   node : (E   : Choice  ) 
       → (Lab : ChoiceSet E → Label)
       → (PE  : ChoiceSet E → ∞Process i A) 
       → (I   : Choice)
       → (PI  : ChoiceSet I → ∞Process i A)
       → (Stat : String )
       → Process+ i A
open Process+



delay : (i : Size) →  {A : Set} → Process i A  → ∞Process (↑ i) A
force (delay i p) j = p
