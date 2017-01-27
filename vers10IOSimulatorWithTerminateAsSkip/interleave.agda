module interleave where 

open import Size
open import process
open Process∞
open Process+
open import choiceSetU
open import choiceAuxFunction
open import dataAuxFunction
open import auxData
open import label
open import Data.String renaming (_++_ to _++s_)
open import showFunction
open import Data.Sum
open import renamingResult

_|||Str_ : String → String → String
s |||Str s' = s ++s " |||  " ++s s'


mutual
   _|||∞_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process∞ i c₀
          → Process∞ i c₁
          → Process∞ i (c₀ ×' c₁)
   forcep (P |||∞  Q) = forcep P  ||| forcep Q     
   Str∞   (P |||∞  Q) = Str∞  P |||Str Str∞ Q

   _|||_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process i c₀
          → Process i c₁
          → Process i (c₀ ×' c₁)
   node P      |||  node Q     = node (P |||++ Q)
   terminate a |||  Q          = fmap (λ b → (a ,, b)) Q
   P           ||| terminate b = fmap (λ a → (a ,, b)) P

   _|||∞+_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process∞ i c₀
          → Process+ i c₁
          → Process∞ i (c₀ ×' c₁)
   forcep (P |||∞+ Q)  = node (forcep P  |||p+ Q)
   Str∞   (P |||∞+  Q) = Str∞  P |||Str Str+ Q

   _|||+∞_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process+ i c₀
          → Process∞ i c₁
          → Process∞ i (c₀ ×' c₁)
   forcep (P |||+∞ Q)   = node (P |||+p  forcep Q )
   Str∞   (P |||+∞  Q)  = Str+  P |||Str Str∞ Q

   _|||p+_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process  i c₀
          → Process+ i c₁
          → Process+  i (c₀ ×' c₁)
   terminate a |||p+ Q = fmap+ (λ b → (a ,, b)) Q
   node P      |||p+ Q = P |||++ Q


   _|||+p_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process+  i c₀
          → Process i c₁
          → Process+  i (c₀ ×' c₁)
   P |||+p terminate b = fmap+ (λ a → (a ,, b)) P
   P |||+p node Q      = P |||++ Q



   _|||++_ : {i : Size}
          → {c₀ c₁ : Choice}
          → Process+ i c₀
          → Process+ i c₁
          → Process+ i (c₀ ×' c₁)
   E    (P |||++ Q)           = E P ⊎' E Q
   Lab  (P |||++ Q) (inj₁ c)  = Lab P c
   Lab  (P |||++ Q) (inj₂ c)  = Lab Q c
   PE   (P |||++ Q) (inj₁ c)  = PE P c |||∞+  Q
   PE   (P |||++ Q) (inj₂ c)  = P      |||+∞  PE Q c
   I    (P |||++ Q)           = I P ⊎' I Q
   PI   (P |||++ Q) (inj₁ c)  = PI P c |||∞+   Q
   PI   (P |||++ Q) (inj₂ c)  = P      |||+∞   PI Q c
   T    (P |||++ Q)           = T P ×' T Q
   PT   (P |||++ Q) (c ,, c₁) = PT P c ,, PT Q c₁
   Str+ (P |||++ Q)           = Str+ P |||Str Str+ Q


infixl 10 _|||∞_  
infixl 10 _|||_  


