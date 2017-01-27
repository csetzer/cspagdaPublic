module cspExample where
open import Size
open import process
open import pro
open ∞Process
open ∞Processx
open Process
open Processx
open import prefix
open import stop
open import skip
open import hid
open import extchoice
open import trx
open Trx
open import ref
--open import extChoiceProof
postulate a b c : Label

lem₁ : ∞Processx _ Choice
lem₁ = b ⟶' Stop' ⊤'   

lem₂ : ∞Processx _ Choice
lem₂ = Stop' ⊤'

lem₃ : ∞Processx _ Choice
lem₃ = (λ b → tt) / lem₁

lem₃' : ∞Processx _ Choice
lem₃' = SKIP' _ ⊤'

lem₄ : Set
lem₄ = lem₂ ⊑ lem₃

lem'₄ : Set
lem'₄ = lem₂ ⊑ lem₃

lem₅ : Set 
lem₅ =  (a ⟶' Stop' ⊤') ⊑ (a ⟶' Stop' ⊤')

lem₅' : lem₅ -- Refinementx _ lem₂ lem₃ 
lem₅' l x  = x 

lem₅'' : Set 
lem₅'' =  (a ⟶' Stop' ⊤') ⊑ (b ⟶' Stop' ⊤')

lem₇ : ∞Processx _ Choice
lem₇ = lem₃

lem₅''' : Set 
lem₅''' =  (b ⟶' Stop' ⊤') ⊑ lem₇

lem₄' : lem₅'''
lem₄' l x = {!!}

lem₆ : ∞Processx _ Choice
lem₆ = a ⟶' Stop' ⊤'

lemₐ : Processx ∞ _
lemₐ = (a ⟶∞ ∞Stop ⊤') □' (b ⟶∞ ∞Stop ⊤') 

lemᵣ : Processx ∞ _
lemᵣ = (b ⟶∞ ∞Stop ⊤') □' (a ⟶∞ ∞Stop ⊤')
{-
lemₙ : lemᵣ ⊑' lemₐ 
lemₙ l x =  refExtChoice' ∞ (b ⟶∞ ∞Stop ⊤') (a ⟶∞ ∞Stop ⊤') l x

-}
