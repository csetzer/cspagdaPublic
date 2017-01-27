module renamingOperator where

open import Size
open import process
open import choiceSetU
open import choiceAuxFunction
open import dataAuxFunction
open import auxData
open import label
open import Data.String renaming (_++_ to _++s_)
open Process+
open Process∞
open import showLabelP

RenameStr : (f : Label → Label) → String → String
RenameStr f s = "(" ++s s ++s  ")" ++s (labelLabelFunToString f)


mutual 
   Rename∞ : {i : Size} → {c : Choice} → (f : Label → Label) → Process∞ i c → Process∞ i c
   forcep (Rename∞ f P)  = Rename f (forcep P)
   Str∞   (Rename∞ f P)  = RenameStr f (Str∞ P)
   
   Rename : {i : Size} → {c : Choice} → (f : Label → Label) → Process i c  → Process i c
   Rename f (node P) = node (Rename+ f P)
   Rename f (terminate x) = terminate x

   Rename+ : {i : Size} → {c : Choice} → (f : Label → Label) → Process+ i c  → Process+ i c
   E    (Rename+ f P)        = (E P) 
   Lab  (Rename+ f P) c      = f (Lab P c) 
   PE   (Rename+ f P) c      = PE P c
   I    (Rename+ f P)        = I P  
   PI   (Rename+ f P) c      = PI P c 
   T    (Rename+ f P)        = T P  
   PT   (Rename+ f P) c      = PT P c 
   Str+ (Rename+ f P)        = RenameStr f (Str+ P)


