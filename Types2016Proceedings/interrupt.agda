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
open import addTick


_△Res_ : Choice → Choice → Choice
c₀ △Res c₁ = (c₀ ⊎' c₁) ⊎' (c₀ ×' c₁)


_△Str_ : String → String → String
s △Str s' = s ++s " \t △ \t " ++s s'




mutual
  _△∞∞_ : {c₀ c₁ : Choice} → {i : Size}
         → Process∞ i c₀ → Process∞ i c₁
         → Process∞ i (c₀ ⊎' c₁)
  forcep (P △∞∞  P')    =  forcep P  △ forcep P' 
  Str∞   (P △∞∞  P')    =  Str∞  P   △Str Str∞  P'

  _△∞+_ : {c₀ c₁  : Choice} → {i : Size}
          → Process∞ i c₀ → Process+ i c₁
          → Process∞ i (c₀ ⊎' c₁)
  forcep (P △∞+  P')   = forcep P  △p+ P'
  Str∞   (P △∞+  P')   = Str∞  P △Str Str+  P'

  _△∞+∞_ : {c₀ c₁  : Choice} → {i : Size}
          → Process∞ i c₀ → Process+ i c₁
          → Process∞ i (c₀ ⊎' c₁)
  forcep (P △∞+∞  P')   = node (forcep P  △p++ P')
  Str∞   (P △∞+∞  P')   = Str∞  P △Str Str+  P'


  _△+∞_ : {c₀ c₁  : Choice} → {i : Size}
          → Process+ i c₀ → Process∞ i c₁
          → Process∞ i  (c₀ ⊎' c₁)
  forcep (P △+∞  P')   = P △+p forcep P' 
  Str∞   (P △+∞  P')   = Str+  P △Str Str∞  P'


  _△+∞∞_ : {c₀ c₁  : Choice} → {i : Size}
          → Process+ i c₀ → Process∞ i c₁
          → Process∞ i  (c₀ ⊎' c₁)
  forcep (P △+∞∞  P')   = node (P △+p+ forcep P')
  Str∞   (P △+∞∞  P')   = Str+  P △Str Str∞  P'



  _△_ : {c₀ c₁  : Choice} → {i : Size}
        → Process i c₀ → Process i c₁
        → Process i (c₀ ⊎' c₁)
  node P      △  P'          = P △+p P'
  P           △  node P'     = P △p+ P'
  terminate a △ terminate b  = 2-✓ a b
            
  _△+p_ : {c₀ c₁  : Choice} → {i : Size}
         → Process+ i c₀ → Process i c₁
         → Process i (c₀ ⊎' c₁)
  P △+p  terminate b  = add✓ (inj₂ b)  
                        (node (fmap+ inj₁ P) )
  P △+p  node P'      = node (P △+ P')

  _△+p+_ : {c₀ c₁  : Choice} → {i : Size}
         → Process+ i c₀ → Process i c₁
         → Process+ i (c₀ ⊎' c₁)
  P △+p+  terminate b  = add✓+ (inj₂ b)(fmap+ inj₁ P) 
  P △+p+  node P'      = P △++ P'



  _△p+_ : {c₀ c₁  : Choice} → {i : Size}
         → Process i c₀ → Process+ i c₁
         → Process i (c₀ ⊎' c₁)
  terminate a △p+  P' = addTimed✓ (inj₁ a)  
                        (node (fmap+ inj₂ P'))
  node      P △p+ P'       = node (P △+ P')

  _△p++_ : {c₀ c₁  : Choice} → {i : Size}
         → Process i c₀ → Process+ i c₁
         → Process+ i (c₀ ⊎' c₁)
  terminate a △p++  P' = addTimed✓+ (inj₁ a)  
                        ((fmap+ inj₂ P'))
  node      P △p++ P'       = P △++ P'


  _△+_ : {c₀ c₁  : Choice} → {i : Size}
         → Process+ i c₀ → Process+ i c₁
         → Process+ i  (c₀ ⊎' c₁)
  E    (P △+ Q)           = E P ⊎' E Q
  Lab  (P △+ Q) (inj₁ x)  = Lab P x
  Lab  (P △+ Q) (inj₂ x)  = Lab Q x
  PE   (P △+ Q) (inj₁ x)  = PE P x △∞+ Q 
  PE   (P △+ Q) (inj₂ x)  = fmap∞ inj₂ (PE Q x)
  I    (P △+ Q)           = I P ⊎' I Q
  PI   (P △+ Q) (inj₁ c)  = PI P c △∞+ Q 
  PI   (P △+ Q) (inj₂ c)  = P      △+∞ PI Q c 
  T    (P △+ Q)           = T P ⊎' T Q
  PT   (P △+ Q) (inj₁ c)  = inj₁ (PT P c)
  PT   (P △+ Q) (inj₂ c)  = inj₂ (PT Q c) 
  Str+ (P △+ Q)           = Str+ P △Str Str+ Q



  _△++_ : {c₀ c₁  : Choice} → {i : Size}
         → Process+ i c₀ → Process+ i c₁
         → Process+ i  (c₀ ⊎' c₁)
  E    (P △++ Q)           = E P ⊎' E Q
  Lab  (P △++ Q) (inj₁ x)  = Lab P x
  Lab  (P △++ Q) (inj₂ x)  = Lab Q x
  PE   (P △++ Q) (inj₁ x)  = PE P x △∞+∞ Q 
  PE   (P △++ Q) (inj₂ x)  = fmap∞ inj₂ (PE Q x)
  I    (P △++ Q)           = I P ⊎' I Q
  PI   (P △++ Q) (inj₁ c)  = PI P c △∞+∞ Q 
  PI   (P △++ Q) (inj₂ c)  = P      △+∞∞ PI Q c 
  T    (P △++ Q)           = T P ⊎' T Q
  PT   (P △++ Q) (inj₁ c)  = inj₁ (PT P c)
  PT   (P △++ Q) (inj₂ c)  = inj₂ (PT Q c) 
  Str+ (P △++ Q)           = Str+ P △Str Str+ Q

