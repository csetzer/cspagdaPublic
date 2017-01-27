{-# OPTIONS --show-implicit #-}

module TraceWithoutSize where

open import Size 
open import Data.List
open import Data.Product
open import Data.Maybe
open import label
open import process
open import choiceSetU



mutual   
 data Tr+  {c : Choice }  :  (l : List Label) → Maybe (ChoiceSet c)
                                       → (P : Process+ ∞ c) → Set where 
   empty  : {P : Process+ ∞ c} → Tr+ [] nothing P
   extc   : {P : Process+ ∞ c}
             → (l : List Label)
             → (tick : Maybe (ChoiceSet c))
             → (x : ChoiceSet (E P))
             → Tr∞ l tick (PE P x)
             → Tr+ (Lab P x ∷ l) tick P
   intc   : {P : Process+ ∞ c}
            → (l : List Label)
            → (tick : Maybe (ChoiceSet c))
            → (x : ChoiceSet (I P))
            → Tr∞ l tick (PI P x)
            → Tr+ l tick P
   terc   : {P : Process+ ∞ c}
            → (x : ChoiceSet (T P))
            → Tr+ [] (just (PT P x)) P

 data Tr {c : Choice } : (l : List Label) → Maybe (ChoiceSet c)
                                     → (P : Process ∞ c) → Set where 
     ter   : (x : ChoiceSet c) → Tr [] (just x) (terminate x)
     empty : (x : ChoiceSet c) → Tr [] nothing (terminate x)
     tnode : {l : List Label}
             → {x : Maybe (ChoiceSet c)}
             → {P : Process+ ∞ c} 
             → Tr+ {c} l x P
             → Tr l x (node P)


 record Tr∞  {c : Choice} (l : List Label) (tick : Maybe (ChoiceSet c))
             (P : Process∞ ∞ c) :  Set  where
        coinductive
        field
         forcet : Tr  l tick (forcep P)

open Tr∞  public



forcet' : {c : Choice} (l : List Label) (tick : Maybe (ChoiceSet c))
          → {P : Process+ ∞ c}  
          → Tr {c} l tick (node P)
          → Tr+ {c} l tick P
forcet' l tick (tnode q) = q


delayt : {c : Choice} (l : List Label) (tick : Maybe (ChoiceSet c))
          → {P : Process+ ∞ c}  
          → Tr+  {c} l tick P
          → Tr∞  {c} l tick (delay  (node  P))
forcet (delayt {c} l tick {P} p) = tnode p



{-
mutual
  downTr+ : {i : Size}{j : Size< i}{c : Choice}(l : List Label)(tick : Maybe (ChoiceSet c))(P : Process+ ∞ c)
            → Tr+ {i} {c} l tick P  → Tr+ {j} {c} l tick P
  downTr+ {i} {j} {c} .[] .nothing P (empty {P = .P}) = empty
  downTr+ {i} {j} {c} .(Lab P x ∷ l) tick P (extc {P = .P} l .tick x x₁) = extc l tick x (downTr∞ {i} {j} l tick (PE P x) x₁)
  downTr+ {i} {j} {c} l tick P (intc {P = .P} .l .tick x x₁) = intc l tick x (downTr∞ {i} {j} l tick (PI P x) x₁)
  downTr+ {i} {j} {c} .[] .(just (PT P x)) P (terc {P = .P} x) = terc x


  downTr∞ : {i : Size}{j : Size< i}{c : Choice}(l : List Label)(tick : Maybe (ChoiceSet c))(P : Process∞ ∞ c)
            → Tr∞ {i} {c} l tick P  → Tr∞ {j} {c} l tick P
  forcet (downTr∞ {i} {j} {c} c₁ l tick tr) = forcet tr



forcet' : {i : Size} {c : Choice} (l : List Label) (tick : Maybe (ChoiceSet c))
          → {P : Process+ i c}  
          → Tr {i} {c} l tick (node P)
          → Tr+ {i} {c} l tick P
forcet' l tick (tnode q) = q


delayt : {i : Size}  {c : Choice} (l : List Label) (tick : Maybe (ChoiceSet c))
          → {P : Process+ i c}  
          → Tr+ {i} {c} l tick P
          → Tr∞ {i} {c} l tick (delay {i} (node {i} P)) -- (delay {!P!}) 
forcet (delayt {i} {c} l tick {P} p) {j} = tnode {j} (downTr+ {c = c} l tick P p)
-}

