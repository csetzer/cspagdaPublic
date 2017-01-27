{-# OPTIONS --copatterns #-}

module extchoice where
open import process 
open import Size
open import pro 
open ∞Processx
open ∞Process
open import renre

--------------------------- Binary External Choice ------------------


mutual 
   extCh : (i : Size) →  {A : Set} → {B : Set} → ∞Process i  A  → ∞Process i B → ∞Process i ((A + B) + (A × B)) 
   force (extCh i x y) j  =   extCh' j (force x j) (force y j) 

   extCh' : (i : Size) → {A : Set} → {B : Set} → Process i  A  →  Process i B → Process i ((A + B) + (A × B))
   extCh' i (node E Lab PE I PI) (node E₁ Lab₁ PE₁ I₁ PI₁)  = node E' Lab' PE' I' PI' where
                                                   E' : Choice 
                                                   E' = E +' E₁

                                                   I' : Choice
                                                   I' = I +' I₁ 

                                                   Lab' :  ChoiceSet E' → Label
                                                   Lab' (inl x) = Lab x
                                                   Lab' (inr x) = Lab₁ x
                                                   
                                                   PE'  : ChoiceSet E' → ∞Process i ((_ + _) + (_ × _))
                                                   force (PE' (inl x)) i = (fmap' i (inl ∘ inl) (force (PE x) i))    
                                                   force (PE' (inr x)) i = (fmap' i (inl ∘ inr) (force (PE₁ x) i))    
                                                     

                                                   PI' : ChoiceSet I' → ∞Process i ((_ + _) + (_ × _))      
                                                   force (PI' (inl x)) i = extCh' i (force (PI x) i) (node E₁ Lab₁ PE₁ I₁ PI₁) 
                                                   force (PI' (inr x)) i = (extCh' i (node E Lab PE I PI) (force (PI₁ x) i)) 
                                                  

   extCh' i (node E Lab PE I PI) (terminate x) = terminate (inl (inr x))
   extCh' i (terminate x) (node E Lab PE I PI) = terminate (inl (inl x))
   extCh' i (terminate x) (terminate x₁) = terminate (inr (x , x₁)) 


_□''_ :  {i : Size} →  {A : Set} → {B : Set} → ∞Process i  A  → ∞Process i B → ∞Process i ((A + B) + (A × B)) 
_□''_ = extCh _

_□'''_ :  {i : Size} → {A : Set} → {B : Set} → Process i  A  →  Process i B → Process i ((A + B) + (A × B))
_□'''_ = extCh' _

--------------------------- Binary External Choice  xversion ------------------


mutual 
   extChx : (i : Size) →  {A : Set} → {B : Set} → ∞Processx i  A  → ∞Processx i B → ∞Processx i ((A + B) + (A × B)) 
   forcex (extChx i x y) j  =   extChx' j (forcex x j) (forcex y j) 

   extChx' : (i : Size) → {A : Set} → {B : Set} → Processx i  A  →  Processx i B → Processx i ((A + B) + (A × B))
   extChx' i {A} {B} (node P) (node Q)  = node (extChNode P Q)
   extChx' i (node (thenode E Lab PE I PI)) (terminate x) = terminate (inl (inr x))
   extChx' i (terminate x) (node (thenode E Lab PE I PI)) = terminate (inl (inl x))
   extChx' i (terminate x) (terminate x₁) = terminate (inr (x , x₁)) 

   extChNode : {i : Size} → {A B : Set} → Node i A → Node i B  → Node i ((A + B) + (A × B))
   extChNode P Q = thenode (extChE' P Q) (extChLab' P Q) (extChPE' P Q) (extChI' P Q) (extChPI' P Q)

   extChE' : {i : Size} → {A B : Set} → Node i A → Node i B  → Choice
   extChE' P Q = (node2E P) +' (node2E Q)

   extChLab' : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Node i B)  → ChoiceSet (extChE' P Q) → Label
   extChLab' P Q (inl x) = node2Lab P x
   extChLab' P Q (inr x) = node2Lab Q x

   extChPE'a : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Node i B)  
               → ChoiceSet (extChE' P Q) →  (j : Size< i) → Processx j ((A + B) + (A × B))
   extChPE'a {i} P Q (inl x) j = fmapx' j (inl ∘ inl) (forcex (node2PE P x) j)  
   extChPE'a {i} P Q (inr x) j = fmapx' j (inl ∘ inr) (forcex (node2PE Q x) j) 


   extChPE' : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Node i B)  
               → ChoiceSet (extChE' P Q) →  ∞Processx i ((A + B) + (A × B))
   forcex (extChPE' P Q x) j = extChPE'a P Q x j


   extChI' : {i : Size} → {A B : Set} → Node i A → Node i B  → Choice
   extChI'  P Q = (node2I P) +' (node2I Q)


   extChPI'toP : (i : Size) → (j : Size< i) → (A B : Set) → (P : Node i A) → (Q : Node i B)  
                  → ChoiceSet (extChI' P Q) →  Processx j A
   extChPI'toP i j A B P Q (inl x) = forcex (node2PI P x) j
   extChPI'toP i j A B P Q (inr x) = node P


   extChPI'toQ : (i : Size) → (j : Size< i) → (A B : Set) → (P : Node i A) → (Q : Node i B)  
                  → ChoiceSet (extChI' P Q) →  Processx j B
   extChPI'toQ i j A B P Q (inl x) = node Q
   extChPI'toQ i j A B P Q (inr x) = forcex (node2PI Q x) j


   extChPI' : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Node i B)  
               → ChoiceSet (extChI' P Q) →  ∞Processx i ((A + B) + (A × B))
   forcex (extChPI' {i}  {A} {B} P Q x) j = extChx' j (extChPI'toP i j A B P Q x) (extChPI'toQ i j A B P Q x)



_□_ : {i : Size} →  {A : Set} → {B : Set} → ∞Processx i  A  → ∞Processx i B → ∞Processx i ((A + B) + (A × B)) 
_□_ = extChx _ 

_□'_ : {i : Size} → {A : Set} → {B : Set} → Processx i  A  →  Processx i B → Processx i ((A + B) + (A × B))
_□'_ = extChx' _


infixl 10 _□_ 
infixl 10 _□'_ 
