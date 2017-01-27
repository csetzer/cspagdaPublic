{-# OPTIONS --copatterns #-}

module hid where
open import process 
open import Size
open import pro 
open ∞Process
open ∞Processx


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
  
                     
_/~_ : {i : Size} → {A : Set} → (hide : Label → Bool) → ∞Process i A → ∞Process i A
_/~_ = Hide _

_/~'_ : {i : Size} → {A : Set} → (hide : Label → Bool) → Process i A → Process i A
_/~'_ = Hide' _





mutual 
   Hidex : (i : Size) → {A : Set} → (hide : Label → Bool) → ∞Processx i A → ∞Processx i A
   forcex (Hidex i f  P) j = Hidex' j f (forcex P j)

   Hidex' : (i : Size) → {A : Set} → (hide : Label → Bool) → Processx i A → Processx i A
   Hidex' i {A} f  (node (thenode E Lab PE I PI)) = node (thenode (subset' E (¬b ∘ (f ∘ Lab))) (Lab ∘ projSubset) (λ x → Hidex i f (PE (projSubset x))) (I +' subset' E (f ∘ Lab)) (λ x → Hidex i {A} f (PI' x)))  where   
          PI' : ChoiceSet  (I +' subset' E (f ∘ Lab)) → ∞Processx i A
          PI' (inl x) = PI x 
          PI' (inr x) = PE (projSubset x) 
   Hidex' i f (terminate x) = terminate x
  
                     
_/_ : {i : Size} → {A : Set} → (hide : Label → Bool) → ∞Processx i A → ∞Processx i A
_/_ = Hidex _

_/'_ : {i : Size} → {A : Set} → (hide : Label → Bool) → Processx i A → Processx i A
_/'_ = Hidex' _


