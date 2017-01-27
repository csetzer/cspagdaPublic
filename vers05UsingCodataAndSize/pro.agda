{-# OPTIONS --copatterns #-}

module pro where
open import process 
open import Size

----------------------Process--------------------------

mutual
   record ∞Process (i : Size) (A : Set) : Set where
     coinductive
     field
       force : (j : Size< i) → Process j A

   
   data Process (i : Size) ( A : Set ) : Set where
       node : (E   : Choice  ) 
           → (Lab : ChoiceSet E → Label)
           → (PE  : ChoiceSet E → ∞Process i A) 
           → (I   : Choice)
           → (PI  : ChoiceSet I → ∞Process i A)
           → Process i A
       terminate : A → Process i A


open ∞Process

delay : (i : Size) →  {A : Set} → Process i A  → ∞Process (↑ i) A
force (delay i p) j = p



----------------------Processx--------------------------

mutual
   record ∞Processx (i : Size) (A : Set) : Set where
     coinductive
     field
       forcex : (j : Size< i) → Processx j A

   
   data Node (i : Size) (A : Set) : Set where
       thenode : (E   : Choice  ) 
           → (Lab : ChoiceSet E → Label)
           → (PE  : ChoiceSet E → ∞Processx i A) 
           → (I   : Choice)
           → (PI  : ChoiceSet I → ∞Processx i A)
           → Node i A


   data Processx (i : Size) ( A : Set ) : Set where
     node : Node i A → Processx i A
     terminate : A → Processx i A

open ∞Processx

delayx : (i : Size) →  {A : Set} → Processx i A  → ∞Processx (↑ i) A
forcex (delayx i p) j = p


node2E : {i : Size} {A : Set} (P : Node i A) →  Choice
node2E (thenode E Lab PE I PI) = E

Node2E : {i : Size} {A : Set} (P : Node i A) →  Set
Node2E P = ChoiceSet (node2E P)

node2Lab : {i : Size} {A : Set} (P : Node i A) → Node2E P → Label
node2Lab (thenode E Lab PE I PI) = Lab

node2PE : {i : Size} {A : Set} (P : Node i A) → Node2E P → ∞Processx i A 
node2PE (thenode E Lab PE I PI) = PE

node2I : {i : Size} {A : Set} (P : Node i A) →  Choice
node2I (thenode E Lab PE I PI) = I

Node2I : {i : Size} {A : Set} (P : Node i A) →  Set
Node2I P = ChoiceSet (node2I P)

node2PI : {i : Size} {A : Set} (P : Node i A) → Node2I P → ∞Processx i A 
node2PI (thenode E Lab PE I PI) = PI


-----------------------------------------Process+--------------------------------------------------------


data Process+ (i : Size) ( A : Set ) : Set where
       node : (E   : Choice  ) 
           → (Lab : ChoiceSet E → Label)
           → (PE  : ChoiceSet E → ∞Process i A) 
           → (I   : Choice)
           → (PI  : ChoiceSet I → ∞Process i A)
           → Process+ i A


