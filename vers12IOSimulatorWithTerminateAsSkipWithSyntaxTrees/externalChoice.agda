module externalChoice where

open import Size
open import process
open Process∞
open Process+
open import choiceSetU
open import choiceAuxFunction
open import dataAuxFunction
open import auxData
open import label
open import renamingResult
open import Size
open import Data.String renaming (_++_ to _++s_)
open import showFunction
open import Data.Sum
open import addTick
open import CSPAgdaSyntax


mutual
  _□∞∞_ : {c₀ c₁  : Choice} → {i : Size} 
          → Process∞ i c₀ → Process∞ i c₁
          → Process∞ i (c₀ ⊎' c₁)
  forcep (P □∞∞  Q)  = forcep P  □  forcep Q  
  Syn∞   (P □∞∞  Q)  = Syn∞ P □' Syn∞ Q

  _□∞+_ : {c₀ c₁  : Choice} → {i : Size} 
          → Process∞ i c₀ → Process+ i c₁
          → Process∞ i  (c₀ ⊎' c₁)
  forcep (P  □∞+  Q)   = forcep  P  □p+   Q
  Syn∞   (P  □∞+  Q)   = Syn∞    P  □'  Syn+ Q 

  _□+∞_ : {c₀ c₁  : Choice} → {i : Size} 
          → Process+ i c₀ → Process∞ i c₁
          → Process∞ i  (c₀ ⊎' c₁)
  forcep  (P  □+∞   Q)  =  P      □+p   forcep Q 
  Syn∞    (P  □+∞   Q)  =  Syn+ P □'  Syn∞ Q 

  _□_ : {c₀ c₁ : Choice} → {i : Size} → Process i c₀
       → Process i c₁ → Process i (c₀ ⊎' c₁)
  node P       □ Q            =   P □+p Q
  P            □ node Q       =   P □p+ Q
  terminate a  □ terminate b  =   2-✓ a b 
 
  _□+p_ : {c₀ c₁ : Choice} → {i : Size} 
          → Process+ i c₀ → Process i c₁ 
          → Process i (c₀ ⊎' c₁)
  P □+p  terminate b  = addTimed✓ (inj₂ b) 
                        (node (fmap+ inj₁ P) )
  P □+p  node Q       =  node (P □+ Q)

  _□p+_ : {c₀ c₁ : Choice} → {i : Size} → Process i c₀
          → Process+ i c₁ → Process i (c₀ ⊎' c₁)
  terminate a □p+  Q = addTimed✓ (inj₁ a)  
                         (node (fmap+ inj₂ Q) )
  node P       □p+  Q  =  node (P □+ Q)


  _□+_ : {c₀ c₁ : Choice} → {i : Size} 
        → Process+ i c₀ → Process+ i c₁  
        → Process+ i (c₀ ⊎' c₁)
  E    (P □+ Q)           = E P ⊎' E Q
  Lab  (P □+ Q) (inj₁ x)  = Lab P x
  Lab  (P □+ Q) (inj₂ x)  = Lab Q x
  PE   (P □+ Q) (inj₁ x)  = fmap∞ inj₁ (PE P x)
  PE   (P □+ Q) (inj₂ x)  = fmap∞ inj₂ (PE Q x)
  I    (P □+ Q)           = I P ⊎'  I Q
  PI   (P □+ Q) (inj₁ c)  = PI P c □∞+ Q 
  PI   (P □+ Q) (inj₂ c)  = P      □+∞ PI Q c 
  T    (P □+ Q)           = T P ⊎' T Q
  PT   (P □+ Q) (inj₁ c)  = inj₁ (PT P c)
  PT   (P □+ Q) (inj₂ c)  = inj₂ (PT Q c)
  Syn+ (P □+ Q)           = Syn+ P □' Syn+ Q 




