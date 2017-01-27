module interrupt where

open import Size
open import process
open import choiceSetU
open import choiceAuxFunction
open import dataAuxFunction
open import auxData
open import label
open import Data.String renaming (_++_ to _++s_)
open import showFunction
open import renamingResult 
open import Data.Sum
open Process∞
open Process+
open import syntaxOfCSPAgda


_△Res_ : Choice → Choice → Choice
c₀ △Res c₁ = (c₀ ⊎' c₁) ⊎' (c₀ ×' c₁)


mutual

  _△∞∞_ : {c₀ c₁  : Choice} → {i : Size} → Process∞ i c₀ → Process∞ i c₁ → Process∞ i (c₀ △Res c₁)
  forcep (P △∞∞  P') = forcep P △ forcep P'  
  Syn∞   (P △∞∞  P') = Syn∞  P △' Syn∞  P'

  _△∞+_ : {c₀ c₁  : Choice} → {i : Size} → Process∞ i c₀ → Process+ i c₁ → Process∞ i (c₀ △Res c₁)
  forcep (P △∞+  P') = forcep P △p+ P'
  Syn∞   (P △∞+  P') = Syn∞  P △' Syn+  P'

  _△+∞_ : {c₀ c₁  : Choice} → {i : Size} → Process+ i c₀ → Process∞ i c₁ → Process∞ i  (c₀ △Res c₁)
  forcep (P △+∞  P') = P △+p forcep P'
  Syn∞   (P △+∞  P') = Syn+  P △' Syn∞  P'

  _△_ : {c₀ c₁  : Choice} → {i : Size} → Process i c₀ → Process i c₁ → Process i (c₀ △Res c₁)
  node P      △ P'      = P △+p P'
  P           △ node P' = P △p+ P'
  terminate a △ terminate b = terminate (inj₂ (a ,, b))

  _△+p_ : {c₀ c₁  : Choice} → {i : Size} → Process+ i c₀ → Process i c₁ → Process i (c₀ △Res c₁)
  P △+p  terminate b  = terminate (inj₁ (inj₂ b)) 
  P △+p  node P'      = node (P △+ P')

  _△p+_ : {c₀ c₁  : Choice} → {i : Size} → Process i c₀ → Process+ i c₁ → Process i (c₀ △Res c₁)
  terminate a △p+  P' = terminate (inj₁ (inj₁ a))
  node P △p+ P'       = node (P △+ P')


  _△+_ : {c₀ c₁  : Choice} → {i : Size} → Process+ i c₀ → Process+ i c₁ → Process+ i  (c₀ △Res c₁)
  E    (P △+ Q)                      = E P ⊎' E Q
  Lab  (P △+ Q) (inj₁ x)             = Lab P x
  Lab  (P △+ Q) (inj₂ x)             = Lab Q x
  PE   (P △+ Q) (inj₁ x)             = PE P x △∞+ Q 
  PE   (_△+_ {c₀}{c₁}{i} P Q) (inj₂ x) = fmap∞ (inj₁ ∘ inj₂) (PE Q x)
  I    (P △+ Q)                      = I P ⊎' I Q
  PI   (P △+ Q) (inj₁ c)             = PI P c △∞+ Q 
  PI   (P △+ Q) (inj₂ c)             = P      △+∞ PI Q c 
  T    (P △+ Q)                      = T P ⊎' T Q
  PT   (P △+ Q) (inj₁ c) = inj₁ (inj₁ (PT P c))
  PT   (P △+ Q) (inj₂ c) = inj₁ (inj₂ (PT Q c)) 
  Syn+ (P △+ Q)                      = Syn+  P △' Syn+  Q

