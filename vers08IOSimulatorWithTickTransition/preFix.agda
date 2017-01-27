module preFix where

open import Size
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import label
open import process
open import choiceSetU
open import showFunction
open import showLabelP
open Process∞
open Process+

mutual
  _⟶_ : {i : Size} → {c : Choice} → Label → Process∞ (↑ i) (ChoiceSet c) → Process (↑ i) (ChoiceSet c)
  _⟶_ {i} {c} l P = node (l ⟶+ P )


  _⟶+_ : {i : Size} → {c : Choice} → Label → Process∞ (↑ i) (ChoiceSet c) → Process+ (↑ i) (ChoiceSet c)
  E   (l ⟶+ P)   = unitc
  Lab (l ⟶+ P) c = l
  PE  (l ⟶+ P) c = P
  I   (l ⟶+ P)   = empty
  PI  (l ⟶+ P) ()
  T   (l ⟶+ P)   = empty
  PT (l ⟶+ P) ()
  Str (l ⟶+ P)   = (showLabel l) ++s " ⟶ " ++s showProcess∞ P 
