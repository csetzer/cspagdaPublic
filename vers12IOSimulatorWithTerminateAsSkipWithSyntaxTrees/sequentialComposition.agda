module sequentialComposition where


open import Size
open import Data.Sum
open import Data.String    renaming (_++_ to _++s_)
open import Data.List.Base renaming (map  to  mapL)
open import choiceSetU
open import process
open Process∞
open Process+
open import showFunction
open import dataAuxFunction
open import CSPAgdaSyntax



mutual 
   _⟫=∞_ : {i : Size} → {c₀ c₁ : Choice} → Process∞ i c₀
          → (ChoiceSet c₀ → Process∞ i c₁)
                      → Process∞ i c₁
   forcep (P ⟫=∞ Q)    =   forcep  P  ⟫= Q
   Syn∞   (P ⟫=∞ Q)    =   Syn∞ P ⟫=' (Syn∞ ∘ Q)

   _⟫=_ : {i : Size} → {c₀ c₁ : Choice} → Process i c₀
          → (ChoiceSet c₀ → Process∞ (↑ i) c₁)
          → Process i c₁
   node      P  ⟫=  Q  =  node    (P ⟫=+ Q)
   terminate x  ⟫=  Q  =  forcep  (Q x) 

   _⟫=+_ : {i : Size} → {c₀ c₁ : Choice} → Process+ i c₀
          → (ChoiceSet c₀ → Process∞ i c₁)
                       → Process+ i c₁
   E    (P ⟫=+ Q)          =  E    P
   Lab  (P ⟫=+ Q)          =  Lab  P
   PE   (P ⟫=+ Q) c        =  PE  P  c  ⟫=∞    Q
   I    (P ⟫=+ Q)          =  I P ⊎' T P
   PI   (P ⟫=+ Q) (inj₁ c) =  PI  P  c  ⟫=∞    Q
   PI   (P ⟫=+ Q) (inj₂ c) =  Q (PT P c)
   T    (P ⟫=+ Q)          =  ∅'
   PT   (P ⟫=+ Q) ()
   Syn+ (P ⟫=+ Q)          =  Syn+ P    ⟫='  (Syn∞  ∘ Q)


_⟫=+p_ : {i : Size} → {c₀ c₁ : Choice} → Process+ i c₀
            → ( ChoiceSet c₀ → Process∞ i c₁)
                       → Process i c₁
P ⟫=+p Q = node (P ⟫=+ Q)
