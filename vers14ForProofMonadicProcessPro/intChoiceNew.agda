module intChoiceNew where


open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import Data.List.Base renaming (map to mapL)
open import Data.Fin
open import Data.Sum
open import Size
open import choiceSetU
open import process
open import showFunction
open import dataAuxFunction
open Process+
open Process∞
open import addTick
open import addTickOperator
open import renamingResult


_⊓Str_  : String → String → String
s ⊓Str s' = "(" ++s s ++s " ⊓  " ++s s' ++s ")"


mutual
 
  _⊓_ : {i : Size} → {c₀ c₁ : Choice} → Process∞ i c₀
        → Process∞ i c₁ →  Process i (c₀ ⊎' c₁) 
  P ⊓  Q =  node (P ⊓∞+ Q)

  _⊓∞_ : {i : Size} → {c₀ c₁ : Choice} → Process∞ i c₀
       → Process∞ i c₁ → Process∞ ( i)  (c₀ ⊎' c₁) 
  forcep (P ⊓∞  Q) {j} =  P  ⊓  Q 
  Str∞   (P ⊓∞  Q)   = (Str∞ P) ⊓Str (Str∞  Q)

  _⊓+_ : {c₀ c₁ : Choice} → {i : Size} 
        → Process+ i c₀ → Process+ i c₁  
        → Process+ i (c₀ ⊎' c₁)
  E    (P ⊓+ Q)     = ∅'
  Lab  (P ⊓+ Q) ()
  PE   (P ⊓+ Q) ()
  I    (P ⊓+ Q)     =  I P ⊎'  I Q
  PI   (P ⊓+ Q) (inj₁ x) = fmap∞ inj₁ (PI P x)
  PI   (P ⊓+ Q) (inj₂ y) = fmap∞ inj₂ (PI Q y)
  T    (P ⊓+ Q)     = ∅'
  PT   (P ⊓+ Q) ()
  Str+ (P ⊓+ Q)     = Str+ P ⊓Str Str+ Q 


  _⊓∞+_ : {c₀ c₁ : Choice} → {i : Size} 
        → Process∞ i c₀ → Process∞ i c₁  
        → Process+ i (c₀ ⊎' c₁)
  E    (P ⊓∞+ Q)                      = ∅'
  Lab  (P ⊓∞+ Q) ()
  PE   (P ⊓∞+ Q) ()
  I    ( _⊓∞+_ {c₀} {c₁} {i} P Q)     = c₀ ⊎' c₁
  PI   (P ⊓∞+ Q) (inj₁ x)             = fmap∞ inj₁ P
  PI   (P ⊓∞+ Q) (inj₂ y)             = fmap∞ inj₂ Q
  T    (P ⊓∞+ Q)                      = ∅'
  PT   (P ⊓∞+ Q) ()
  Str+ (P ⊓∞+ Q)                      = Str∞ P ⊓Str Str∞ Q 
