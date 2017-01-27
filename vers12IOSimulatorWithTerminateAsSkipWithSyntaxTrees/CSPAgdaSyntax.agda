module CSPAgdaSyntax where

open import Data.Nat  
open import label
open import choiceSetU
open import Size
open import Data.Bool
open import Data.Sum
open import dataAuxFunction
open import showLabelP
open import Data.List.Base renaming (map to mapL)
open import Data.String  renaming (_++_ to _++s_)
open import Data.Bool renaming (T to True)


data Syntax : Choice → Set where
  namedArg   : {c : Choice} → String → Syntax c
  terminate' : {c : Choice } → ChoiceSet c → Syntax c
  _⟫='_      : {c c₀ : Choice} → Syntax c → (ChoiceSet c → Syntax c₀) → Syntax c₀
  _⟶'_       : {c : Choice} → Label  → Syntax c → Syntax c
  _|||'_     : {c c₀ : Choice} → Syntax c → Syntax c₀ → Syntax (c ×' c₀) 
  _□'_       : {c c₀ : Choice} → Syntax c → Syntax c₀ → Syntax (c ⊎' c₀) 
  _⊓'_       : {c : Choice} → Syntax c → Syntax c → Syntax c
  _/'_       : {c : Choice} → (f : Label → Bool) → Syntax c → Syntax c
  Hide'      : {c : Choice} → (f : Label → Bool) → Syntax c → Syntax c
  Hide''     : {c : Choice} → (f : Label → Bool) → String → Syntax c → Syntax c
  Rename'    : {c : Choice} → (f : Label → Label) → Syntax c → Syntax c
  [[_]]_     : {c : Choice} → (f : Label → Label) → Syntax c → Syntax c
  SKIP''     : {c : Choice} → (a : ChoiceSet c) → Syntax c
  STOP''     : {c : Choice} → Syntax c
  _△'_       : {c  c₀ : Choice} → Syntax c → Syntax c₀ → Syntax (c ⊎' c₀)
  rec'       : {c₀ c₁ : Choice} → (ChoiceSet c₀ → Syntax (c₀ ⊎' c₁)) → ChoiceSet c₀ →  Syntax c₁
  fmaps      : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → Syntax c₀ → Syntax c₁
  MSKIP'     : {c   t : Choice} → (f : ChoiceSet t → ChoiceSet c) →  Syntax c
  SKIPL'     : {c : Choice} → List (ChoiceSet c) →  Syntax c
  addTick'   : {ca c : Choice} → (f : ChoiceSet c → ChoiceSet ca) →  Syntax ca →  Syntax ca
  RenameSyn' : {c : Choice} → (f : Label → Label) → Syntax c → Syntax c
  IntChoice' : {c : Choice} → {c₀ : Choice} → (f : ChoiceSet c₀ → Syntax c)  → Syntax c
  Parallel'  : {c c₀ : Choice} → (indepP indepQ : Label → Bool) → (interLeaved : Label → Label → Bool)
               → (interLeavedToLabel : (PLab QLab : Label)  → True (interLeaved PLab QLab) → Label)
               → Syntax c → Syntax c₀ → Syntax (c ×' c₀)
  add✓'      : {c : Choice} →  (a : ChoiceSet c) → Syntax c  → Syntax c
  2-✓'       : {c₀ c₁ : Choice} → (a : ChoiceSet c₀) → (a' : ChoiceSet c₁)  → Syntax (c₀ ⊎' c₁)
  addTimed✓' : {c : Choice} → (a : ChoiceSet c)  → Syntax c  → Syntax c
  DIV'        : {c : Choice} → Syntax c
  _↾'_        : {c : Choice} → Syntax c → (A : Label → Bool) → Syntax c
  _[_]||'[_]_ : {c c₀ : Choice} →  Syntax c → (A  B : Label → Bool) → Syntax c₀  → Syntax (c ×' c₀)



choice2Str2Str' : {c : Choice} → (f : ChoiceSet c →  String)  → String
choice2Str2Str'   {c} f =  unlinesWithChosenString " " (mapL ((λ x → "(λ "  
                                                                  ++s (choice2Str x) 
                                                                  ++s " → " 
                                                                  ++s f x 
                                                                  ++s ")")) 
                               (choice2Enum c)) 
  
 


ToString : {c : Choice} → Syntax c → String
ToString (namedArg str)          = str
ToString (terminate' a)          = choice2Str a
ToString (P ⟫=' Q)               = "(" ++s ToString P ++s "  ;  " ++s choice2Str2Str' (λ x → ToString (Q x)) ++s ")"  
ToString (l ⟶' Q)                = "(" ++s showLabel l ++s " ⟶  " ++s ToString Q  ++s")"
ToString (P |||' Q)              = "(" ++s ToString P ++s " ||| " ++s ToString Q  ++s")"
ToString (P □' Q)                = "(" ++s ToString P ++s "  □  " ++s ToString Q  ++s")"
ToString (P ⊓' Q)                = "(" ++s ToString P ++s "  ⊓  " ++s ToString Q  ++s")"
ToString (f /' Q)                = "(" ++s "Hide  " ++s (labelBoolFunToString f) ++s " " ++s ToString Q ++s ")"
ToString (Hide' f Q)             = "(" ++s "Hide  " ++s (labelBoolFunToString f) ++s " " ++s ToString Q ++s ")"
ToString (Hide'' f s Q)          = "(" ++s "Hide  " ++s s ++s "  " ++s ToString Q ++s")"
ToString (Rename' f Q)           = "(" ++s ToString Q ++s  ")" ++s (labelLabelFunToString f)
ToString ([[ f ]]  Q)            = "([[" ++s (labelLabelFunToString f) ++s"]])" ++s ToString Q 
ToString (SKIP'' a)              = "(" ++s "SKIP(" ++s choice2Str a ++s ")" ++s ")" 
ToString STOP''                  = "STOP"
ToString (P △' Q)                = "(" ++s ToString P ++s " △  "  ++s ToString Q  ++s ")"
ToString (rec' f c)              = "rec(" ++s choice2Str2Str' (λ x → ToString (f x)) ++s "," ++s choice2Str c ++s ")"
ToString (fmaps f P)             = "fmap(" ++s choice2Str2Str' (λ x → choice2Str (f x)) ++s "," ++s ToString P  ++s ")"
ToString (MSKIP' f)              = "MSKIP+" ++s "???"
ToString (SKIPL' l)              = "SKIPL"  ++s "???"
ToString (addTick' f P)          = "???"
ToString (RenameSyn' f s)        = "(" ++s ToString s ++s  ")" ++s (labelLabelFunToString f)
ToString (IntChoice' f)          = " \t ⊔ \t " ++s choice2Str2Str' (λ x → ToString (f x))
ToString (Parallel' a b I Iₗ P Q) = "???"
ToString (add✓' a syn)           =  "(add✓ " ++s choice2Str a ++s " " ++s ToString syn ++s ")"
ToString (2-✓' a a')             =  "(2-✓ "++s choice2Str a ++s " " ++s choice2Str a' ++s ")"
ToString (addTimed✓' a syn)      = "(addTimed✓ " ++s choice2Str a ++s " " ++s ToString syn ++s ")"
ToString (DIV')                  = "DIV"
ToString (syn ↾' A)              =  labelBoolFunToString A ++s " ↾ " ++s ToString syn
ToString (s [ A ]||'[ B ] t)  = ToString s ++s "[" ++s labelBoolFunToString A ++s "]||[" ++s labelBoolFunToString A ++s "]" ++s ToString t 





reduceComp : {c c₁ : Choice} → Syntax c → (ChoiceSet c → Syntax c₁) → Syntax c₁
reduceComp (l ⟶' P) Q = l ⟶' reduceComp P Q
reduceComp STOP'' Q = STOP''
reduceComp (terminate' a) Q = Q a
reduceComp (P ⟫=' P') Q = reduceComp P (λ x  → reduceComp (P' x) Q)
reduceComp (P ⊓' P') Q = reduceComp P Q ⊓' reduceComp P' Q
reduceComp P Q = P ⟫=' Q



reducefmap : {c c₁ : Choice} → (f : ChoiceSet c → ChoiceSet c₁ ) → Syntax c → Syntax c₁
reducefmap f (l ⟶' P)  = l ⟶' reducefmap  f P
reducefmap f (P ⟫=' Q)   = P  ⟫=' (λ x → reducefmap f (Q x))
reducefmap f (P ⊓' Q)   = reducefmap f P ⊓'  reducefmap f Q
reducefmap f (terminate' a) = terminate' (f a)
reducefmap f (fmaps g P) = reducefmap (f ∘ g) P
reducefmap f STOP''     = STOP''
reducefmap f P          = fmaps f P

reduceSyntax : {c : Choice} → Syntax c → Syntax c
reduceSyntax (l ⟶' P)  = l ⟶' reduceSyntax P
reduceSyntax (fmaps f P) = reducefmap f (reduceSyntax P)
reduceSyntax (P  ⟫=' Q) = reduceComp (reduceSyntax  P) (λ x  → reduceSyntax  (Q x))
reduceSyntax s = s











{-
semantics : {i : Size} → {c : Choice} → Syntax → Process i c
semantics (P ⟫=' Q)      = {!!}
semantics (l ⟶' P)     = l ⟶ delay (semantics P)
semantics (P |||' Q)    = {!!}
semantics (P □' Q)      = {!!}
semantics (P ⊓' Q)      = forcep (delay (semantics P) ⊔∞ delay (semantics Q))
semantics (Hide' f x)   = {!!}
semantics (Rename' f x) = {!!}
semantics (SKIP'' a)    = SKIP {!a!} 
semantics STOP''        = {!!}
semantics (P △ Q)       = {!!}


reduce : Syntax → Syntax
reduce (  (l ⟶' P) ⟫='  f =    l ⟶' (P ⟫='  f)
reduce (  (l ⟶' P) ⟫='  f =    l ⟶' (P ⟫='  f)

-}



{-
reduceExt :  {c₀ c₁  : Choice} → Syntax c₀ → Syntax c₁ → Syntax (c₀ ⊎' c₁)
reduceExt (namedArg x) c₂ = {!c₂!}
reduceExt (terminate' x) c₂ = {!!}
reduceExt (c₂ ⟫=' x) c₃ = {!!}
reduceExt (x ⟶' c) c₂ = {!!}
reduceExt (c₂ |||' c₃) c₄ = {!!}
reduceExt (c₂ □' c₃) c₄ = {!!}
reduceExt (c ⊓' c₂) c₃ = {!!}
reduceExt (f /' c) c₂ = {!!}
reduceExt (Hide' f c) c₂ = {!!}
reduceExt (Hide'' f x c) c₂ = {!!}
reduceExt (Rename' f c) c₂ = {!!}
reduceExt ([[ f ]] c) c₂ = {!!}
reduceExt (SKIP'' a) c₂ = {!!}
reduceExt STOP'' c₂ = {!!}
reduceExt (c₂ △' c₃) c₄ = {!!}
reduceExt (rec' x x₁) c₃ = {!!}
reduceExt (fmaps f c) c₃ = {!!}
reduceExt (MSKIP' f) c₂ = {!!}
reduceExt (SKIPL' x) c₂ = {!!}
reduceExt (addTick' f c₂) c₃ = {!!}
reduceExt (RenameSyn' f c) c₂ = {!!}
reduceExt (IntChoice' f) c₃ = {!!}
reduceExt (Parallel' indepP indepQ interLeaved interLeavedToLabel c₂ c₃) c₄ = {!!}
reduceExt (add✓' a c) c₂ = {!!}
reduceExt (2-✓' a a') c₃ = {!!}
reduceExt (addTimed✓' a c) c₂ = {!!}
reduceExt DIV' c₂ = {!!}
reduceExt (c ↾' A) c₂ = {!!}
reduceExt (c₂ [ A ]||'[ B ] c₃) c₄ = {!!} 
-}
