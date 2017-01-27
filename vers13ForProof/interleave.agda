module interleave where 

open import Size
open import process
open Process∞
open Process'
open Process
open import choiceSetU
open import auxData
open import Data.Sum


_|||'_ : {i : Size} → {c₀ c₁ : Choice} → Process' i c₀
          → Process' i c₁ → Process' i (c₀ ×' c₁)
E    (P |||' Q)            =  E P ⊎' E Q
Lab  (P |||' Q) (inj₁ c)   =  Lab P c
Lab  (P |||' Q) (inj₂ c)   =  Lab Q c
PE   (P |||' Q) (inj₁ c)   =  PE P c |||'  Q
PE   (P |||' Q) (inj₂ c)   =  P  |||' PE Q c
I    (P |||' Q)            =  I P ⊎' I Q
PI   (P |||' Q) (inj₁ c)   =  PI P c |||'   Q
PI   (P |||' Q) (inj₂ c)   =  P  |||' PI Q c
T    (P |||' Q)            =  T P ×' T Q
PT   (P |||' Q) (c ,, c₁)  =  PT P c ,, PT Q c₁

mutual

  _|||_ : {i : Size} → {c₀ c₁ : Choice} → Process i c₀
          → Process i c₁ → Process i (c₀ ×' c₁)
  E    (P ||| Q)            =  E P ⊎' E Q
  Lab  (P ||| Q) (inj₁ c)   =  Lab P c
  Lab  (P ||| Q) (inj₂ c)   =  Lab Q c
  PE   (P ||| Q) (inj₁ c)   =  PE P c |||∞p   Q
  PE   (P ||| Q) (inj₂ c)   =  P  |||p∞ PE Q c
  I    (P ||| Q)            =  I P ⊎' I Q
  PI   (P ||| Q) (inj₁ c)   =  PI P c |||∞p   Q
  PI   (P ||| Q) (inj₂ c)   =  P  |||p∞ PI Q c
  T    (P ||| Q)            =  T P ×' T Q
  PT   (P ||| Q) (c ,, c₁)  =  PT P c ,, PT Q c₁

  _|||∞_ : {i : Size} → {c₀ c₁ : Choice} → Process∞  i c₀
          → Process∞ i c₁ → Process∞ i (c₀ ×' c₁)
  forcep (P |||∞  Q)  = forcep P ||| forcep Q


  _|||p∞_ : {i : Size} → {c₀ c₁ : Choice} → Process i c₀
          → Process∞ i c₁ → Process∞ i (c₀ ×' c₁)
  forcep (P |||p∞  Q) = P ||| forcep Q

  _|||∞p_ : {i : Size} → {c₀ c₁ : Choice} → Process∞ i c₀
          → Process i c₁ → Process∞ i (c₀ ×' c₁)
  forcep (P |||∞p  Q) = forcep P ||| Q
  


infixl 10  _|||'_  
infixl 10  _|||_  
infixl 10  _|||∞_  
infix  10  _|||p∞_  
infix  10  _|||∞p_  


