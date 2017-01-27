module renamingProcess where

open import Data.String
open import Size
open import process
open Process∞
open Process+
open import choiceSetU


mutual
  renameP∞ : {i : Size} → {c : Choice} → String → Process∞ i c → Process∞ i c
  forcep (renameP∞ s P)  = renameP s (forcep P)
  Str∞   (renameP∞ s P)  = s

  renameP : {i : Size} → {c : Choice} → String → Process i c  
            → Process i c
  renameP s (node P) = node (renameP+ s P)
  renameP s (terminate x) = terminate x

  renameP+ : {i : Size} → {c : Choice} → String → Process+ i c  
             → Process+ i c
  E    (renameP+ s P)        = (E P) 
  Lab  (renameP+ s P) c      = Lab P c 
  PE   (renameP+ s P) c      = PE P c
  I    (renameP+ s P)        = I P  
  PI   (renameP+ s P) c      = PI P c 
  T    (renameP+ s P)        = T P  
  PT   (renameP+ s P) c      = PT P c 
  Str+ (renameP+ s P)        = s


