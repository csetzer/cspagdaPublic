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
open import addTickOperator

_□Res_ : Choice → Choice → Choice
c₀ □Res c₁ = (c₀ ⊎' c₁) ⊎' (c₀ ×' c₁)


_□Str_  : String → String → String
s □Str s' = "(" ++s s ++s " □  " ++s s' ++s ")"


mutual
  _□∞∞_ : {c₀ c₁  : Choice} → {i : Size} 
          → Process∞ i c₀ → Process∞ i c₁ → Process∞ i (c₀ □Res c₁)
  forcep (P □∞∞  Q) = forcep P □ forcep Q  
  Str∞   (P □∞∞  Q) = Str∞ P □Str Str∞ Q

  _□∞+_ : {c₀ c₁  : Choice} → {i : Size} 
          → Process∞ i c₀ → Process+ i c₁ → Process∞ i  (c₀ □Res c₁)
  forcep (P □∞+  Q) = forcep P □p+ Q
  Str∞   (P □∞+  Q) = Str∞ P □Str Str+ Q 

  _□+∞_ : {c₀ c₁  : Choice} → {i : Size} 
          → Process+ i c₀ → Process∞ i  c₁ → Process∞ i  (c₀ □Res c₁)
  forcep (P □+∞  Q) = P □+p forcep Q   
  Str∞   (P □+∞  Q) = Str+ P □Str Str∞ Q 

  _□_ : {c₀ c₁  : Choice} → {i : Size} 
        → Process i c₀ → Process i c₁ → Process i (c₀ □Res c₁)
  node P      □ Q           =  P □+p Q
  P           □ node Q      =  P □p+ Q
  terminate a □ terminate b = terminate (inj₂ (a ,, b))
  -- maybe this should be a process which can terminate with a and with bx
  -- however that violates the principle from processes with T P = empty dont
 

  _□+p_ :{c₀ c₁  : Choice} → {i : Size} 
         → Process+ i c₀ → Process i c₁ → Process i (c₀ □Res c₁)
  P □+p  terminate b  = node (fmap+ ((λ a → inj₂ (a ,, b))) P) 
  P □+p  node Q      =  node (P □+ Q)


  -- alternative code  we thought it violates the principle from processes with T P = empty dont
  -- create processes with T P = nonempty
  --   P □+p  terminate b  = addTick (fin 1) (λ x → (inj₁ (inj₂ b))) (node (fmap+ ((λ a → inj₂ (a ,, b))) P) )
  _□p+_ : {c₀ c₁  : Choice} → {i : Size} 
          → Process i c₀ → Process+ i c₁ → Process i  (c₀ □Res c₁)
  terminate a □p+  Q = node (fmap+ ((λ b → inj₂ (a ,, b))) Q)
  node P □p+ Q       = node (P □+ Q)

   -- alternative code  we thought it violates the principle from processes with T P = empty dont
   -- create processes with T P = nonempty
   -- terminate a □p+  Q =  addTick (fin 1) (λ x → (inj₁ (inj₁ a))) (node (fmap+ ((λ b → inj₂ (a ,, b))) Q) )



  _□+_ : {c₀ c₁  : Choice} → {i : Size} 
         → Process+ i c₀ → Process+ i c₁ → Process+ i (c₀ □Res c₁)
  E    (P □+ Q)          = E P ⊎' E Q
  Lab  (P □+ Q) (inj₁ x) = Lab P x
  Lab  (P □+ Q) (inj₂ x) = Lab Q x
  PE   (P □+ Q) (inj₁ x) = fmapCustom∞ (inj₁ ∘ inj₁) "(inl ∘ inl)" (PE P x)
  PE   (P □+ Q) (inj₂ x) = fmapCustom∞ (inj₁ ∘ inj₂) "(inl ∘ inr)" (PE Q x)
  I    (P □+ Q)          = I P ⊎'  I Q
  PI   (P □+ Q) (inj₁ c) = PI P c □∞+ Q 
  PI   (P □+ Q) (inj₂ c) = P      □+∞ PI Q c 
  T    (P □+ Q)          = T P ⊎' T Q
  PT   (P □+ Q) (inj₁ c) = inj₁ (inj₁ (PT P c))
  PT   (P □+ Q) (inj₂ c) = inj₁ (inj₂ (PT Q c))
  Str+ (P □+ Q)          = Str+ P □Str Str+ Q 



{-
□Res : Set → Set → Set
□Res A B = (A ⊎ B) ⊎ (A × B)


mutual
  _□∞∞_ : {A B  : Set} → {i : Size} → Process∞ i A → Process∞ i B → Process∞ i (□Res A B)
  forcep (P □∞∞  Q) = forcep P □ forcep Q 

  _□∞+_ : {A B : Set} → {i : Size} → Process∞ i A → Process+ i B → Process∞ i (□Res A B)
  forcep (P □∞+  Q) = forcep P □p+ Q

  _□+∞_ : {A : Set} → {B : Set} → {i : Size} → Process+ i A → Process∞ i B → Process∞ i (□Res A B)
  forcep (P □+∞  Q) = P □+p forcep Q 

  _□_ : {A B : Set} → {i : Size} → Process i A → Process i B → Process i (□Res A B)
  node P      □ Q      = P □+p Q
  P           □ node Q = P □p+ Q
  terminate a □ terminate b = terminate (inj₂ (a ,, b))
  -- maybe this should be a process which can terminate with a and with bx
  -- however that violates the principle from processes with T P = empty dont
 

  _□+p_ : {A B : Set} → {i : Size} → Process+ i A → Process i B → Process i (□Res A B)
  P □+p  terminate b  = node (fmap+ ((λ a → inj₂ (a ,, b))) P) 
  P □+p  node Q      = node (P □+ Q)


  -- alternative code  we thought it violates the principle from processes with T P = empty dont
  -- create processes with T P = nonempty
  --   P □+p  terminate b  = addTick (fin 1) (λ x → (inj₁ (inj₂ b))) (node (fmap+ ((λ a → inj₂ (a ,, b))) P) )
  _□p+_ : {A B : Set} → {i : Size} → Process i A → Process+ i B → Process i (□Res A B)
  terminate a □p+  Q = node (fmap+ ((λ b → inj₂ (a ,, b))) Q)
  node P □p+ Q       = node (P □+ Q)

   -- alternative code  we thought it violates the principle from processes with T P = empty dont
   -- create processes with T P = nonempty
   -- terminate a □p+  Q =  addTick (fin 1) (λ x → (inj₁ (inj₁ a))) (node (fmap+ ((λ b → inj₂ (a ,, b))) Q) )



  _□+_ : {A B : Set} → {i : Size} → Process+ i A → Process+ i B → Process+ i (□Res A B)
  E    (P □+ Q)          = E P ⊎' E Q
  Lab  (P □+ Q) (inj₁ x) = Lab P x
  Lab  (P □+ Q) (inj₂ x) = Lab Q x
  PE   (P □+ Q) (inj₁ x) = fmap∞ (inj₁ ∘ inj₁) (PE P x)
  PE   (P □+ Q) (inj₂ x) = fmap∞ (inj₁ ∘ inj₂) (PE Q x)
  I    (P □+ Q)          = I P ⊎'  I Q
  PI   (P □+ Q) (inj₁ c) = PI P c □∞+ Q 
  PI   (P □+ Q) (inj₂ c) = P      □+∞ PI Q c 
  T    (P □+ Q)          = T P ⊎' T Q
  PT   (P □+ Q) (inj₁ c) = inj₁ (inj₁ (PT P c))
  PT   (P □+ Q) (inj₂ c) = inj₁ (inj₂ (PT Q c))
  Str+ (P □+ Q)          = (Str+ P ++s " \t □ \t " ++s Str+ Q)
-}
