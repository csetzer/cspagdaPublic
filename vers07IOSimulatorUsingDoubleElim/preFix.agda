module preFix where


open import Size
open import Data.Sum
open import Data.Bool
open import Data.Bool.Base
open import Data.Nat
open import Agda.Builtin.Nat renaming (_<_ to _<N_; _==_ to _==N_)
open import Data.Fin renaming (_+_ to _+,_;_<_ to _<F_)
open import Data.Char renaming (_==_ to _==?_)
open import Data.Maybe
open import Data.Nat 
open import Data.List
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import Data.Nat.Show renaming (show to showℕ)
open import SizedIO.Base  renaming (force to forceIO; delay to delayIO)
open import SizedIO.Console hiding (main)
open import NativeIO
open import Agda.Builtin.Unit
open import Data.List.Base renaming (map to mapL)
open import label
open import process
open Process∞
open Process+


open import dataAuxFunction
open import auxData 
open import choiceSetU
open import showFunction
open import showLabelP


mutual
  _⟶_ : {i : Size} → {c : Choice} → Label → Process∞ (↑ i) (ChoiceSet c) → Process (↑ i) (ChoiceSet c)
  _⟶_ {i} {c} l P = node (l ⟶+ P )


  _⟶+_ : {i : Size} → {c : Choice} → Label → Process∞ (↑ i) (ChoiceSet c) → Process+ (↑ i) (ChoiceSet c)
  E   (l ⟶+ P)   = fin 1
  Lab (l ⟶+ P) c = l
  PE  (l ⟶+ P) c = P
  I   (l ⟶+ P)   = fin 0
  PI (l ⟶+ P) ()
  Str (l ⟶+ P)   = (showLabel l) ++s "\t ⟶ \t" ++s showProcess∞ P 
