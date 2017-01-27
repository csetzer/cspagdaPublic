module syntaxOfCSPAgda where

open import Data.Nat  
open import label
open import choiceSetU
open import Size
open import Data.Bool
open import dataAuxFunction
open import showLabelP
open import Data.List.Base renaming (map to mapL)
open import Data.String  renaming (_++_ to _++s_)

open import Data.Bool renaming (T to True)




data Syntax : Set where
  namedArg   : String → Syntax
  terminate' : { c : Choice } → ChoiceSet c → Syntax 
  _⟫='_       : Syntax → {c : Choice} → (ChoiceSet c → Syntax) → Syntax
  _⟶'_      : Label  → Syntax → Syntax
  _|||'_     : Syntax → Syntax → Syntax
  _□'_       : Syntax → Syntax → Syntax
  _⊓'_       : Syntax → Syntax → Syntax
  Hide'      : (f : Label → Bool) → Syntax → Syntax
  Hide''     : (f : Label → Bool) → String → Syntax → Syntax
  Rename'    : (f : Label → Label) → Syntax → Syntax
  SKIP''     : {c : Choice} → (a : ChoiceSet c) → Syntax
  STOP''     : Syntax
  _△'_       : Syntax → Syntax → Syntax
  rec'       : {c : Choice} → (ChoiceSet c → Syntax) → ChoiceSet c →  Syntax 
  fmaps      : {c₀ c₁ : Choice} → (f : ChoiceSet c₀ → ChoiceSet c₁) → Syntax → Syntax
  MSKIP'     : {c t : Choice} → (f : ChoiceSet t → ChoiceSet c) →  Syntax
  SKIPL'     : {i : Size} → {c : Choice} → List (ChoiceSet c) →  Syntax
  addTick'   : {ca : Choice} → {i : Size} → (c : Choice) → (f : ChoiceSet c → ChoiceSet ca) →  Syntax →  Syntax
  RenameSyn' : (f : Label → Label) → Syntax → Syntax
  IntChoice' : {c : Choice} → (f : ChoiceSet c → Syntax)  → Syntax
  Parallel'  : (indepP indepQ : Label → Bool) → (interLeaved : Label → Label → Bool) → (interLeavedToLabel : (PLab QLab : Label) 
                → True (interLeaved PLab QLab) → Label) → Syntax → Syntax → Syntax





choice2Str2Str' : {c : Choice} → (f : ChoiceSet c →  String)  → String
choice2Str2Str'   {c} f =  unlinesWithChosenString " " (mapL ((λ x → "(λ "  
                                                                  ++s (choice2Str x) 
                                                                  ++s " → " 
                                                                  ++s f x 
                                                                  ++s ")")) 
                               (choice2Enum c)) 
  
 

ToString : Syntax → String
ToString (namedArg str)          = str
ToString (terminate' a)          = choice2Str a
ToString (P ⟫=' Q)                = "(" ++s ToString P ++s "  ;  " ++s choice2Str2Str' (λ x → ToString (Q x)) ++s ")"  
ToString (l ⟶' Q)               = "(" ++s showLabel l ++s " ⟶ " ++s ToString Q  ++s")"
ToString (P |||' Q)              = "(" ++s ToString P ++s " ||| " ++s ToString Q  ++s")"
ToString (P □' Q)                = "(" ++s ToString P ++s "  □  " ++s ToString Q  ++s")"
ToString (P ⊓' Q)                = "(" ++s ToString P ++s "  ⊓  " ++s ToString Q  ++s")"
ToString (Hide' f Q)             = "(" ++s "Hide  " ++s (labelBoolFunToString f) ++s " " ++s ToString Q ++s ")"
ToString (Hide'' f s Q)          = "(" ++s "Hide  " ++s s ++s "  " ++s ToString Q ++s")"
ToString (Rename' f Q)           = "(" ++s ToString Q ++s  ")" ++s (labelLabelFunToString f)
ToString (SKIP'' a)              = "(" ++s "SKIP(" ++s choice2Str a ++s ")" ++s ")" 
ToString STOP''                  = "STOP"
ToString (P △' Q)                = "(" ++s ToString P ++s " △  "  ++s ToString Q  ++s ")"
ToString (rec' f c)              = "rec(" ++s choice2Str2Str' (λ x → ToString (f x)) ++s "," ++s choice2Str c ++s ")"
ToString (fmaps f P)             = "fmap(" ++s choice2Str2Str' (λ x → choice2Str (f x)) ++s "," ++s ToString P  ++s ")"
ToString (MSKIP' f)              = "MSKIP+" ++s "???"
ToString (SKIPL' l)              = "SKIPL"  ++s "???"
ToString (addTick' c f P)        = "???"
ToString (RenameSyn' f s)        = "(" ++s ToString s ++s  ")" ++s (labelLabelFunToString f)
ToString (IntChoice' f)          = " \t ⊔ \t " ++s choice2Str2Str' (λ x → ToString (f x))
ToString (Parallel' a b I Iₗ P Q) = "???"


































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


