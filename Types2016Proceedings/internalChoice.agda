module internalChoice where 


open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import Data.List.Base renaming (map to mapL)
open import Data.Fin
open import Size
open import choiceSetU
open import process
open import showFunction
open import dataAuxFunction
open Process+
open Process∞


bool : Choice
bool = fin 2  

if_then_else : {A : Set} → ChoiceSet bool → A → A → A
if zero then a else b = a
if (suc zero) then a else b = b
if (suc (suc ())) then a else b

_⊓Str_ : String → String → String
s ⊓Str s' =  "(" ++s s ++s " ⊓ " ++s s' ++s ")"



_⊓+_ : {i : Size} → {c : Choice} → Process∞ i c
       → Process∞ i c → Process+ i c
P ⊓+ Q = process+ ∅' efq efq bool (λ b → if b then P else Q) ∅' efq
           (Str∞ P ⊓Str Str∞ Q)


_⊓+'_ : {i : Size} → {c : Choice} → Process∞ i c 
      → Process∞ i c → Process+ i c
E    (P ⊓+' Q)              = ∅'
Lab  (P ⊓+' Q) ()  
PE   (P ⊓+' Q) () 
I    (P ⊓+' Q)              = fin 2
PI   (P ⊓+' Q) zero         = P
PI   (P ⊓+' Q) (suc zero)   = Q
PI   (P ⊓+' Q) (suc (suc ())) 
T    (P ⊓+' Q)              = ∅'
PT   (P ⊓+' Q) () 
Str+ (P ⊓+' Q)              = Str∞ P  ⊓Str Str∞ Q


{-
_⊓++_ : {i : Size} → {c : Choice} → Process+ i c 
      → Process+ i c → Process+ i c
E    (P ⊓++ Q)              = ∅'
Lab  (P ⊓++ Q) ()  
PE   (P ⊓++ Q) () 
I    (P ⊓++ Q)              = fin 2
PI   (P ⊓++ Q) zero         = {!P!}
PI   (P ⊓++ Q) (suc zero)   = PI Q {!1!} -- Q
PI   (P ⊓++ Q) (suc (suc ())) 
T    (P ⊓++ Q)              = ∅'
PT   (P ⊓++ Q) () 
Str+ (P ⊓++ Q)              = Str+ P  ⊓Str Str+ Q
-}



_⊓_ : {i : Size} → {c : Choice} → Process∞ i c
      → Process∞ i c → Process i c 
P ⊓  Q = node (P ⊓+  Q)

_⊓∞_ : {i : Size} → {c : Choice} → Process∞ i c
       → Process∞ i c → Process∞ (↑ i) c 
forcep (P ⊓∞  Q) {j} = P  ⊓ Q 
Str∞   (P ⊓∞  Q)   = (Str∞ P) ⊓Str (Str∞  Q)




mutual
  IntChoiceStr : {c : Choice} → (f : ChoiceSet c → String)  → String
  IntChoiceStr f =  " \t ⊓ \t " ++s choice2Str2Str f  

  IntChoice∞ : (i : Size) → {c₀ : Choice} → (c : Choice) 
          → (PI : ChoiceSet c → Process∞ i c₀) 
          → Process∞ (↑ i) c₀  
  forcep (IntChoice∞ i c PI) {j} = IntChoice j c PI
  Str∞   (IntChoice∞ i c PI)   = IntChoiceStr (Str∞ ∘ PI)

  IntChoice : (i : Size) → {c₀ : Choice} → (c : Choice) 
          → (PI : ChoiceSet c → Process∞ i c₀)
          → Process i c₀  
  IntChoice i c PI = node (IntChoice+ i c PI)

  IntChoice+ : (i : Size) → {c₀ : Choice} → (c : Choice) 
          → (P : ChoiceSet c → Process∞ i c₀) 
          → Process+ i c₀  
  E    (IntChoice+ i c P)  = ∅'
  Lab  (IntChoice+ i c P)  = efq 
  PE   (IntChoice+ i c P)  = efq 
  I    (IntChoice+ i c P)  = c
  PI   (IntChoice+ i c P)  = P 
  T    (IntChoice+ i c P)  = ∅'
  PT   (IntChoice+ i c P)  = efq      
  Str+ (IntChoice+ i c P)  = IntChoiceStr (Str∞ ∘ P)
