module hidingOperator where 

open import Size 
open import process 
open ∞Process
open import label
open import Data.Bool
open import auxData
open import dataAuxFunction
open import choiceSetU



mutual 
   Hide : (i : Size) → {c : Choice}
          → (hide : Label → Bool)
          → ∞Process i (ChoiceSet c)
          → ∞Process i (ChoiceSet c)
   force (Hide i f  P) j = Hide' j f (force P j)

   Hide' : (i : Size) → {c : Choice} 
           → (hide : Label → Bool)
           → Process i (ChoiceSet c)
           → Process i (ChoiceSet c)
   Hide' i {c} f (node E Lab PE I PI Stat) =
                                                  node ((subset' E (¬b ∘ (f ∘ Lab))))
                                                  ((Lab ∘ projSubset))
                                                  ((λ x → Hide i f (PE (projSubset x))))
                                                  ((I +'' subset' E (f ∘ Lab)))
                                                  ((λ x → Hide i {c} f (PI' x)))
                                                  {!!} where   
          PI' : ChoiceSet (I +'' subset' E (f ∘ Lab))
                → ∞Process i (ChoiceSet c)
          PI' (inl x) = PI x 
          PI' (inr x) = PE (projSubset x) 
   Hide' i f (terminate x) = terminate x
