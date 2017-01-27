{-# OPTIONS --show-implicit #-}

module indTr where

open import Size 
open import Data.List
open import Data.Product
open import Data.Maybe
open import label
open import process
open import choiceSetU

postulate TODO : {A : Set} → A

mutual   
 data Tr+ {i : Size} {c : Choice }  :  (l : List Label) → Maybe (ChoiceSet c)
                                       → (P : Process+ i c) → Set where 
   empty  : {P : Process+ i c} → Tr+ [] nothing P
   extc   : {P : Process+ i c}
             → (l : List Label)
             → (tick : Maybe (ChoiceSet c))
             → (x : ChoiceSet (E P))
             → Tr∞ l tick (PE P x)
             → Tr+ (Lab P x ∷ l) tick P
   intc   : {P : Process+ i c}
            → (l : List Label)
            → (tick : Maybe (ChoiceSet c))
            → (x : ChoiceSet (I P))
            → Tr∞ l tick (PI P x)
            → Tr+ l tick P
   terc   : {P : Process+ i c}
            → (x : ChoiceSet (T P))
            → Tr+ [] (just (PT P x)) P

 data Tr {i : Size} {c : Choice } : (l : List Label) → Maybe (ChoiceSet c)
                                     → (P : Process i c) → Set where 
     ter   : (x : ChoiceSet c) → Tr [] (just x) (terminate x)
     empty : (x : ChoiceSet c) → Tr [] nothing (terminate x)
     tnode : {l : List Label}
             → {x : Maybe (ChoiceSet c)}
             → {P : Process+ i c} 
             → Tr+ {i} {c} l x P
             → Tr l x (node P)


 record Tr∞  {i : Size} {c : Choice} (l : List Label) (tick : Maybe (ChoiceSet c))
             (P : Process∞ i c) :  Set  where
        coinductive
        field
         forcet :  {j : Size< i} → Tr {j} l tick (forcep P)

open Tr∞  public

mutual
  downTr+ : {i : Size}{j : Size< i}{c : Choice}(l : List Label)(tick : Maybe (ChoiceSet c))(P : Process+ i c)
            → Tr+ {i} {c} l tick P  → Tr+ {j} {c} l tick P
  downTr+ {i} {j} {c} .[] .nothing P (empty {P = .P}) = empty
  downTr+ {i} {j} {c} .(Lab P x ∷ l) tick P (extc {P = .P} l .tick x x₁) = extc l tick x (downTr∞ {i} {j} l tick (PE P x) x₁)
  downTr+ {i} {j} {c} l tick P (intc {P = .P} .l .tick x x₁) = intc l tick x (downTr∞ {i} {j} l tick (PI P x) x₁)
  downTr+ {i} {j} {c} .[] .(just (PT P x)) P (terc {P = .P} x) = terc x


  downTr∞ : {i : Size}{j : Size< i}{c : Choice}(l : List Label)(tick : Maybe (ChoiceSet c))(P : Process∞ i c)
            → Tr∞ {i} {c} l tick P  → Tr∞ {j} {c} l tick P
  forcet (downTr∞ {i} {j} {c} c₁ l tick tr) = forcet tr

{-
  downTr : {i : Size}{j : Size< i}{c : Choice}(l : List Label)(tick : Maybe (ChoiceSet c))(P : Process i c)
            → Tr {i} {c} l tick P  → Tr {j} {c} l tick P
  downTr {i} {j} {c} .[] .(just x) .(terminate x) (ter x) = ter x
  downTr {i} {j} {c} .[] .nothing .(terminate x) (empty x) = empty x
  downTr {i} {j} {c} c₁ l .(node P) (tnode {l = .c₁} {x = .l} {P = P} x) = {!!} -- forcet (downTr∞ c₁ l (delay (node P)) {!!}) --tr
-}




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

{-
delayt : {i : Size} {c : Choice} (l : List Label) (tick : Maybe (ChoiceSet
c))
          → {P : Process∞ i c}  
          → Tr+ {i} {c} l tick {!P!} 
          → Tr∞ {i} {c} l tick P -- (delay {!P!}) 
delayt l tick p =  {!!} 
-}



{- This is actually not provable unless you know P has a termination event`


terp : {i : Size} {c : Choice} (tick : ChoiceSet c) (P : Process+ i c)
       → Tr {i} {c} [] (just tick) (node P)
terp {i} {c} tick P = tnode TODO

ter∞ : {i : Size} {c : Choice} (tick : ChoiceSet c) (P : Process∞ i c)
       → Tr∞ {i} {c} [] (just tick) P
forcet (ter∞ {i} {c} tick P) = TODO 

-}
