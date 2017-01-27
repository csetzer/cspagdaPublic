{-# OPTIONS --copatterns #-}

module int where
open import process 
open import Size
open import pro
open ∞Process
open ∞Processx
open import renre


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

