module externalChoice where


{-check the check sign-}

open import Size
open import process
open ∞Process
open import choiceSetU
open import choiceAuxFunction
open import dataAuxFunction
open import auxData
open import label
open import renamingResult
open import Size
open import Data.String renaming (_++_ to _++s_)
open import showFunction


            
mutual 
   extCh : (i : Size) →  {c₀ : Choice} → {c₁  : Choice} → ∞Process i  (ChoiceSet c₀)  → ∞Process i (ChoiceSet c₁ ) → ∞Process i ((ChoiceSet c₀ +'  ChoiceSet c₁ ) +' (ChoiceSet c₀ × ChoiceSet c₁ )) 
   force (extCh i {c₀} {c₁} x y) j  =   extCh' j {c₀} {c₁} (force x j) (force y j) 

   extCh' : (i : Size) → {c₀ : Choice} → {c₁  : Choice} → Process i ( ChoiceSet c₀)  →  Process i (ChoiceSet c₁ ) → Process i ((ChoiceSet c₀ +' ChoiceSet c₁ ) +' (ChoiceSet c₀ × ChoiceSet c₁ ))
   extCh' i {c₀} {c₁} (node E Lab PE I PI Stat) (node E₁ Lab₁ PE₁ I₁ PI₁ Stat₁) = node E' Lab' PE' I' PI' (Stat ++s " \t □ \t " ++s Stat₁) where
                                                   E' : Choice 
                                                   E' = E +'' E₁

                                                   I' : Choice
                                                   I' = I +'' I₁ 

                                                   Lab' :  ChoiceSet E' → Label
                                                   Lab' (inl x) = Lab x
                                                   Lab' (inr x) = Lab₁ x
                                                  
                                                   PE'  :  ChoiceSet E' → ∞Process i ((_ +' _) +' (_ × _))
                                                   force (PE' (inl x)) i = (fmap' i (inl ∘ inl) (force (PE x) i))    
                                                   force (PE' (inr x)) i = (fmap' i (inl ∘ inr) (force (PE₁ x) i))    
                                                    

                                                   PI' : ChoiceSet I' → ∞Process i ((_ +' _) +' (_ × _))      
                                                   force (PI' (inl x)) i = extCh' i {c₀} {c₁}  (force (PI x) i) (node E₁ Lab₁ PE₁ I₁ PI₁ Stat) 
                                                   force (PI' (inr x)) i = (extCh' i {c₀} {c₁}  (node E Lab PE I PI Stat) (force (PI₁ x) i)) 
                                                  

   extCh' i {c₀}{c₁} (node E Lab PE I PI Stat) (terminate b) = node E Lab PE' I PI' (Stat ++s showProcess c₁ (terminate b)) where  {-check Stat-}               
                                                   PE' : ChoiceSet E
                                                        → ∞Process i ((ChoiceSet c₀ +'  ChoiceSet c₁ ) +' (ChoiceSet c₀ × ChoiceSet c₁ ))
                                                   force (PE' x) i = (fmap' i (λ a → inr ( a , b)) (force (PE x) i))

                                                   PI' : ChoiceSet I
                                                        → ∞Process i ((ChoiceSet c₀ +'  ChoiceSet c₁ ) +' (ChoiceSet c₀ × ChoiceSet c₁ ))
                                                   force (PI' x) i = (fmap' i (λ a → inr ( a , b)) (force (PI x) i))


   extCh' i {c₀}{c₁} (terminate a) (node E Lab PE I PI Stat) = node E Lab PE' I PI' (showProcess c₀ (terminate a) ++s Stat) where  {-check Stat-}
                                                  PE'  : ChoiceSet E
                                                        → ∞Process i ((ChoiceSet c₀ +'  ChoiceSet c₁ ) +' (ChoiceSet c₀ × ChoiceSet c₁ ))
                                                  force (PE' x) i = (fmap' i (λ b → inr ( a , b)) (force (PE x) i))

                                                  PI' : ChoiceSet I
                                                        → ∞Process i ((ChoiceSet c₀ +'  ChoiceSet c₁ ) +' (ChoiceSet c₀ × ChoiceSet c₁ ))
                                                  force (PI' x) i = (fmap' i (λ b → inr ( a , b)) (force (PI x) i))
                                                 
   extCh' i (terminate x) (terminate x₁) = terminate (inr (x , x₁))


_□∞_ :  {i : Size} →  {c₀ : Choice} → {c₁  : Choice} → ∞Process i  (ChoiceSet c₀)  → ∞Process i (ChoiceSet c₁ ) → ∞Process i ((ChoiceSet c₀ +' ChoiceSet c₁ ) +' (ChoiceSet c₀ × ChoiceSet c₁ )) 
_□∞_ {i} {c₀} {c₁} = extCh i {c₀} {c₁} 


_□_ :  {i : Size} → {c₀ : Choice} → {c₁  : Choice} → Process i  (ChoiceSet c₀)  →  Process i (ChoiceSet c₁ ) → Process i ((ChoiceSet c₀ +' ChoiceSet c₁ ) +' (ChoiceSet c₀ × ChoiceSet c₁ ))
_□_ {i} {c₀} {c₁} = extCh' i {c₀} {c₁} 


infixl 10  _□∞_
infixl 10  _□_
