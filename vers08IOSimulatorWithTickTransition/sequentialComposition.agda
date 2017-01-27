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

funcChoice2ProcessToProcess : ∀ {i} → (c d : Choice) → (ChoiceSet c  → Process i (ChoiceSet d)) → String
funcChoice2ProcessToProcess c d f = unlines (mapL ((λ x → "λ "  ++s (choice2String c x) ++s " → " ++s showProcess d (f x) ++s ")"))
                                    (choice2Enumeration0 c))

funcChoice2ProcessToProcess∞ : ∀ {i} → (c d : Choice) → (ChoiceSet c  → Process∞ (↑ i)  (ChoiceSet d)) → String
funcChoice2ProcessToProcess∞ {i} c d f = funcChoice2ProcessToProcess c d (λ x → forcep (f x ) i )

funcChoice2ProcessToProcess∞' : ∀ {i} → {c d : Choice} → (ChoiceSet c  → Process∞ (↑ i)  (ChoiceSet d)) → String
funcChoice2ProcessToProcess∞' {i} {c} {d} f = funcChoice2ProcessToProcess∞ c d f


mutual 
   _⟫=∞_ : {i : Size} →  {c₀ c₁ : Choice} → Process∞ i (ChoiceSet c₀)  → (ChoiceSet c₀ → Process∞ i (ChoiceSet c₁))
                      → Process∞ i (ChoiceSet c₁)
   forcep (P ⟫=∞ Q) j  =   forcep P j ⟫= Q

   _⟫=_ : {i : Size} → {c₀ c₁ : Choice} → Process i (ChoiceSet c₀)  → (ChoiceSet c₀ → Process∞ (↑ i) (ChoiceSet c₁))
                       → Process i (ChoiceSet c₁)
   node P ⟫= Q              = node (P ⟫=+ Q)
   _⟫=_ {i} (terminate x) Q = forcep (Q x) i 

   _⟫=+_ : {i : Size} → {c₀ c₁ : Choice} → Process+ i (ChoiceSet c₀)  → (ChoiceSet c₀ → Process∞ (↑ i) (ChoiceSet c₁))
                       → Process+ i (ChoiceSet c₁)
   E   (P ⟫=+ Q)           = E P
   Lab (P ⟫=+ Q)           = Lab P
   PE  (P ⟫=+ Q) c         = PE P c ⟫=∞ Q
   I   (P ⟫=+ Q)           = I P +'' T P
   PI  (P ⟫=+ Q) (inj₁ c)  = PI P c ⟫=∞ Q
   PI  (P ⟫=+ Q) (inj₂ c)  = Q (PT P c)
   T   (P ⟫=+ Q)           = empty
   PT (P ⟫=+ Q) ()
   Str (P ⟫=+ Q)           = Str P  ++s ";" ++s funcChoice2ProcessToProcess∞' Q



_⟫=++_ : {i : Size} → {c₀ c₁ : Choice} → Process+ i (ChoiceSet c₀)
            → ( ChoiceSet c₀ → Process∞ i (ChoiceSet c₁))
                       → Process+ i (ChoiceSet c₁)
E   (P ⟫=++ Q)    = E P
Lab (P ⟫=++ Q) x  = Lab P x
PE  (P ⟫=++ Q) x  = PE P x ⟫=∞ Q
I   (P ⟫=++ Q)    = I P  +'' T P
PI  (P ⟫=++ Q) (inj₁ x)  = PI P x ⟫=∞ Q
PI  (P ⟫=++ Q) (inj₂ x)  = Q (PT P x)
T   (P ⟫=++ Q)    = empty
PT (P ⟫=++ Q) ()
Str (P ⟫=++ Q)    = Str P ++s "⟫=++ Something"

_⟫=+p_ : {i : Size} → {c₀ c₁ : Choice} → Process+ i (ChoiceSet c₀)
            → ( ChoiceSet c₀ → Process∞ i (ChoiceSet c₁))
                       → Process i (ChoiceSet c₁)
P ⟫=+p Q = node (P ⟫=++ Q)


{-
   postulate _⟫=∞'_ : {i : Size} →  {c₀ c₁ : Choice} → Process∞ (↑ i) (ChoiceSet c₀)  → (ChoiceSet c₀ → Process∞ (↑ i) (ChoiceSet c₁))
                      → Process∞ (↑ (↑ i)) (ChoiceSet c₁)
   -- forcep (P ⟫=∞' Q) j  =   {!!} -- forcep P j ⟫= Q


   _⟫=+'_ : {i : Size} → {c₀ c₁ : Choice} → Process+ (↑ (↑ i)) (ChoiceSet c₀)  → (ChoiceSet c₀ → Process∞ (↑ i) (ChoiceSet c₁))
                       → Process+ (↑ (↑ i)) (ChoiceSet c₁)
   E   (P ⟫=+' Q)           = E P
   Lab (P ⟫=+' Q)           = Lab P
   PE  (P ⟫=+' Q) c         = PE P c  ⟫=∞' Q 
   I   (P ⟫=+' Q)           = I P -- TODO   +'' T P
   PI  (P ⟫=+' Q) c  = PI P c ⟫=∞' Q
--   PI  (P ⟫=+' Q) (inj₂ c)  = {!!} -- Q (PT P c)
   T   (P ⟫=+' Q)           = empty
   PT (P ⟫=+' Q) ()
   Str (P ⟫=+' Q)           = Str P  -- ++s ";" ++s funcChoice2ProcessToProcess∞' Q
-}
