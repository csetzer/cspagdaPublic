module parallel where 

open import Size 
open import process 
open ∞Process
open import label
open import Data.Bool
open import auxData
open import dataAuxFunction
open import choiceSetU


mutual
   Parallel : (i : Size)
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → (c₀ c₁ : Choice)
          → ∞Process i (ChoiceSet c₀)
          → ∞Process i (ChoiceSet c₁)
          → ∞Process i (ChoiceSet c₀ × ChoiceSet c₁)

   force (Parallel i indepP indepQ interLeaved interLeavedToLabel c₀ c₁ P Q) j =
                  Parallel' j indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                                                         (force P j) (force Q j)  


   Parallel' : (i : Size)
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          
          → (c₀ c₁ : Choice)
          → Process i (ChoiceSet c₀)
          → Process i (ChoiceSet c₁)
          → Process i (ChoiceSet c₀ × ChoiceSet c₁)


   Parallel' i indepP indepQ interLeaved interLeavedToLabel c₀ c₁
             (node E₁ Lab₁ PE₁ I₁ PI₁ Stat₁) (node E₂ Lab₂ PE₂ I₂ PI₂ Stat₂) =
                                              node E' Lab' PE' I' PI' {!!}  where
           E₁' : Choice 
           E₁' = subset' E₁ (indepP ∘ Lab₁) +'' subset' E₂ (indepQ ∘ Lab₂) 
              
           f₁ : ChoiceSet (E₁ ×' E₂) →  Bool
           f₁ ( e₁ , e₂ ) = interLeaved (Lab₁ e₁) (Lab₂ e₂)

           E₂' : Choice
           E₂' = subset' (E₁ ×' E₂) f₁

           E' : Choice
           E' =  E₁' +'' E₂' 

           Lab' : ChoiceSet E' →  Label
           Lab' (inl (inl (sub e _)))  = Lab₁ e
           Lab' (inl (inr (sub e _)))  = Lab₂ e
           Lab' (inr (sub (e₁ , e₂) cond)) = interLeavedToLabel (Lab₁ e₁) (Lab₂ e₂) cond


                                                  
           PE' : ChoiceSet E' → ∞Process i (ChoiceSet c₀ × ChoiceSet c₁)                                                         
           force (PE' (inl (inl (sub e x)))) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                                                     (force (PE₁ e) j) (node E₂ Lab₂ PE₂ I₂ PI₂ Stat₂)
           force (PE' (inl (inr (sub e x)))) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                                                     (node E₁ Lab₁ PE₁ I₁ PI₁ Stat₁) (force (PE₂ e) j)
           force (PE' (inr (sub (e₁ , e₂) x))) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                                                                 (force (PE₁ e₁) j) (force (PE₂ e₂) j)

           I' : Choice 
           I' = I₁ +'' I₂

           PI' : ChoiceSet I' → ∞Process i (ChoiceSet c₀ × ChoiceSet c₁)
           force (PI' (inl x)) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                                                    (force (PI₁ x) j) (node E₂ Lab₂ PE₂ I₂ PI₂ Stat₂)
           force (PI' (inr x)) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                                                    (node E₁ Lab₁ PE₁ I₁ PI₁ Stat₁) (force (PI₂ x) j)

   Parallel' i indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                 (node E₁ Lab₁ PE₁ I₁ PI₁ Stat) (terminate b) = node E₁ Lab₁ PE' I₁ PI' {!!}
       where
         PE' : ChoiceSet E₁ → ∞Process i (ChoiceSet c₀ × ChoiceSet c₁)
         force (PE' e) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                                                              (force (PE₁ e) j) (terminate b) 
        
         PI' : ChoiceSet I₁ → ∞Process i (ChoiceSet c₀ × ChoiceSet c₁)
         force (PI' i') j = Parallel' j indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                                                               (force (PI₁ i') j) (terminate b)
   
   Parallel' i indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                                 (terminate a) (node E₂ Lab₂ PE₂ I₂ PI₂ Stat) =
                                                            node E₂ Lab₂ PE' I₂ PI' {!!}
       where
        PE' : ChoiceSet E₂ → ∞Process i (ChoiceSet c₀ × ChoiceSet c₁) 
        force (PE' e) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                                                               (terminate a) (force (PE₂ e) j)

        PI' : ChoiceSet I₂ → ∞Process i  (ChoiceSet c₀ × ChoiceSet c₁)
        force (PI' i') j = Parallel' j indepP indepQ interLeaved interLeavedToLabel c₀ c₁
                                                               (terminate a) (force (PI₂ i') j)   
   Parallel' i indepP indepQ interLeaved interLeavedToLabel A B
                                                (terminate a) (terminate b) = terminate (a , b)         

