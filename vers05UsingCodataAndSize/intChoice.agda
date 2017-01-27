{-# OPTIONS --copatterns #-}

module intChoice where
open import process 
open import Size
open import pro 
open ∞Process 
open ∞Processx 


---- Internal Choice Operation -------------

IntChoice : (i : Size) → {A : Set} → (I : Choice) 
          → (PI : ChoiceSet I → ∞Process i A) 
          → ∞Process i A 
force (IntChoice i I PI) j = node ∅' efq efq I (λ x → PI x) 



Int : {i : Size} → {A : Set} → (I : Choice) 
       → (PI : ChoiceSet I → ∞Process i A) 
       → ∞Process i A 
Int = IntChoice _



open import prefix
open import stop
open import skip

x₁ : ∞Process _ Choice
x₁ = Stop ⊤'

x₂ : ∞Process _ Choice 
x₂ = Skip ⊤'


x₃ : ∞Process _ Choice 
x₃ = IntChoice _ Bool' (λ x → x₁) 

