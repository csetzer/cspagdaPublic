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

_⟫=Str_ : {c₀ : Choice} → String → (ChoiceSet c₀ → String) → String
s ⟫=Str f = s  ++s ";" ++s choice2Str2Str f


mutual 
   _⟫=∞_ : {i : Size} →  {c₀ c₁ : Choice} → Process∞ i c₀  → (ChoiceSet c₀ → Process∞ i c₁)
                      → Process∞ i c₁
   forcep (P ⟫=∞ Q) =   forcep P ⟫= Q
   Str∞   (P ⟫=∞ Q) =   Str∞ P ⟫=Str (Str∞ ∘ Q)

   _⟫=_ : {i : Size} → {c₀ c₁ : Choice} → Process i c₀  → (ChoiceSet c₀ → Process∞ (↑ i) c₁)
                       → Process i c₁
   node P ⟫= Q              = node (P ⟫=+ Q)
   _⟫=_ {i} (terminate x) Q = forcep (Q x)  
   _⟫=+_ : {i : Size} → {c₀ c₁ : Choice} → Process+ i c₀  → (ChoiceSet c₀ → Process∞ i c₁)
                       → Process+ i c₁
   E    (P ⟫=+ Q)           = E P
   Lab  (P ⟫=+ Q)           = Lab P
   PE   (P ⟫=+ Q) c         = PE P c ⟫=∞ Q
   I    (P ⟫=+ Q)           = I P ⊎' T P
   PI   (P ⟫=+ Q) (inj₁ c)  = PI P c ⟫=∞ Q
   PI   (P ⟫=+ Q) (inj₂ c)  = Q (PT P c)
   T    (P ⟫=+ Q)           = ∅'
   PT   (P ⟫=+ Q) ()
   Str+ (P ⟫=+ Q)           = Str+ P ⟫=Str (Str∞  ∘ Q)  -- Str+ P  ++s ";" ++s funcChoice2ProcessToProcess∞' Q



_⟫=+p_ : {i : Size} → {c₀ c₁ : Choice} → Process+ i c₀
            → ( ChoiceSet c₀ → Process∞ i c₁)
                       → Process i c₁
P ⟫=+p Q = node (P ⟫=+ Q)


{-

_⟫=++_ : {i : Size} → {c₀ c₁ : Choice} → Process+ i c₀
            → ( ChoiceSet c₀ → Process∞ i c₁)
                       → Process+ i c₁
E    (P ⟫=++ Q)    = E P
Lab  (P ⟫=++ Q) x  = Lab P x
PE   (P ⟫=++ Q) x  = PE P x ⟫=∞ Q
I    (P ⟫=++ Q)    = I P  ⊎' T P
PI   (P ⟫=++ Q) (inj₁ x)  = PI P x ⟫=∞ Q
PI   (P ⟫=++ Q) (inj₂ x)  = Q (PT P x)
T    (P ⟫=++ Q)    = ∅'
PT   (P ⟫=++ Q) ()
Str+ (P ⟫=++ Q)    = Str+ P ++s "⟫=++ Something"

   postulate _⟫=∞'_ : {i : Size} →  {c₀ c₁ : Choice} → Process∞ (↑ i) c₀  → (ChoiceSet c₀ → Process∞ (↑ i) c₁)
                      → Process∞ (↑ (↑ i)) c₁
   -- forcep (P ⟫=∞' Q)  =   {!!} -- forcep P  ⟫= Q


   _⟫=+'_ : {i : Size} → {c₀ c₁ : Choice} → Process+ (↑ (↑ i)) c₀  → (ChoiceSet c₀ → Process∞ (↑ i) c₁)
                       → Process+ (↑ (↑ i)) c₁
   E   (P ⟫=+' Q)           = E P
   Lab (P ⟫=+' Q)           = Lab P
   PE  (P ⟫=+' Q) c         = PE P c  ⟫=∞' Q 
   I   (P ⟫=+' Q)           = I P -- TODO   ⊎' T P
   PI  (P ⟫=+' Q) c  = PI P c ⟫=∞' Q
--   PI  (P ⟫=+' Q) (inj₂ c)  = {!!} -- Q (PT P c)
   T   (P ⟫=+' Q)           = ∅'
   PT (P ⟫=+' Q) ()
   Str (P ⟫=+' Q)           = Str P  -- ++s ";" ++s funcChoice2ProcessToProcess∞' Q
-}
