{-# OPTIONS --copatterns #-}

module par where
open import process 
open import Size
open import pro 
open import renre
open ∞Process
open ∞Processx

-------Parallel Operation -----------------------

mutual
   Parallel : (i : Size)
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → (A B : Set)
          → ∞Process i A
          → ∞Process i B
          → ∞Process i (A × B)

   force (Parallel i indepP indepQ interLeaved interLeavedToLabel A B P Q) j =
          Parallel' j indepP indepQ interLeaved interLeavedToLabel A B (force P j) (force Q j)  


   Parallel' : (i : Size)
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          
          → (A B : Set)
          → Process i A
          → Process i B
          → Process i (A × B)


   Parallel' i indepP indepQ interLeaved interLeavedToLabel A B (node E₁ Lab₁ PE₁ I₁ PI₁) (node E₂ Lab₂ PE₂ I₂ PI₂) = node E' Lab' PE' I' PI'  where
           E₁' : Choice 
           E₁' = subset' E₁ (indepP ∘ Lab₁) +' subset' E₂ (indepQ ∘ Lab₂)
              
           f₁ : ChoiceSet (E₁ ×' E₂) →  Bool
           f₁ ( e₁ , e₂ ) = interLeaved (Lab₁ e₁) (Lab₂ e₂)

           E₂' : Choice
           E₂' = subset' (E₁ ×' E₂) f₁

           E' : Choice
           E' = E₁' +' E₂'

           Lab' : ChoiceSet E' →  Label
           Lab' (inl (inl (sub e _)))  = Lab₁ e
           Lab' (inl (inr (sub e _)))  = Lab₂ e
           Lab' (inr (sub (e₁ , e₂) cond)) = interLeavedToLabel (Lab₁ e₁) (Lab₂ e₂) cond

                                                  
           PE' : ChoiceSet E' → ∞Process i (A × B)                                                         
           force (PE' (inl (inl (sub e x)))) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                                                    (force (PE₁ e) j) (node E₂ Lab₂ PE₂ I₂ PI₂)
           force (PE' (inl (inr (sub e x)))) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                                                    (node E₁ Lab₁ PE₁ I₁ PI₁) (force (PE₂ e) j)
           force (PE' (inr (sub (e₁ , e₂) x))) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                                                      (force (PE₁ e₁) j) (force (PE₂ e₂) j)

           I' : Choice 
           I' = I₁ +' I₂

           PI' : ChoiceSet I' → ∞Process i (A × B)
           force (PI' (inl x)) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                                                    (force (PI₁ x) j) (node E₂ Lab₂ PE₂ I₂ PI₂)
           force (PI' (inr x)) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                                                    (node E₁ Lab₁ PE₁ I₁ PI₁) (force (PI₂ x) j)

   Parallel' i indepP indepQ interLeaved interLeavedToLabel A B (node E₁ Lab₁ PE₁ I₁ PI₁) (terminate b) = node E₁ Lab₁ PE' I₁ PI'
       where
         PE' : ChoiceSet E₁ → ∞Process i (A × B)
         force (PE' e) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B (force (PE₁ e) j) (terminate b) 
        
         PI' : ChoiceSet I₁ → ∞Process i (A × B)
         force (PI' i') j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B (force (PI₁ i') j) (terminate b)
   
   Parallel' i indepP indepQ interLeaved interLeavedToLabel A B (terminate a) (node E₂ Lab₂ PE₂ I₂ PI₂) = node E₂ Lab₂ PE' I₂ PI'
       where
        PE' : ChoiceSet E₂ → ∞Process i (A × B) 
        force (PE' e) j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                            (terminate a) (force (PE₂ e) j)

        PI' : ChoiceSet I₂ → ∞Process i (A × B)
        force (PI' i') j = Parallel' j indepP indepQ interLeaved interLeavedToLabel A B
                            (terminate a) (force (PI₂ i') j)   
   Parallel' i indepP indepQ interLeaved interLeavedToLabel A B (terminate a) (terminate b) = terminate (a , b)         






parallel : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label)
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → (A B : Set)
          → ∞Process i A
          → ∞Process i B
          → ∞Process i (A × B)

parallel = Parallel _ 


parallel' : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          
          → (A B : Set)
          → Process i A
          → Process i B
          → Process i (A × B)

parallel' = Parallel' _

---------------------------Parallel---------------------------------

mutual
   Parallelx : (i : Size)
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → (A B : Set)
          → ∞Processx i A
          → ∞Processx i B
          → ∞Processx i (A × B)

   forcex (Parallelx i indepP indepQ interLeaved interLeavedToLabel A B P Q) j =
          Parallelx' j indepP indepQ interLeaved interLeavedToLabel A B (forcex P j) (forcex Q j)  


   Parallelx' : (i : Size)
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → (A B : Set)
          → Processx i A
          → Processx i B
          → Processx i (A × B)


   Parallelx' i indepP indepQ interLeaved interLeavedToLabel A B (node P) (node Q) = node (ParNode indepP indepQ interLeaved interLeavedToLabel P Q)  
   Parallelx' i indepP indepQ interLeaved interLeavedToLabel A B (node P) (terminate b) = fmapx' i (λ a → (a , b)) (node P)

   Parallelx' i indepP indepQ interLeaved interLeavedToLabel A B (terminate a) (node Q) = fmapx' i (λ b → (a , b)) (node Q)

   Parallelx' i indepP indepQ interLeaved interLeavedToLabel A B (terminate P) (terminate Q) = terminate (P , Q)


   ParNode : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
                                   → Node i A → Node i B  → Node i (A × B)
   ParNode indepP indepQ interLeaved interLeavedToLabel P Q = thenode (parE indepP indepQ interLeaved interLeavedToLabel P Q) (parLab' indepP indepQ interLeaved interLeavedToLabel P Q) (parPEE' indepP indepQ interLeaved interLeavedToLabel P Q ) (I'' P Q) (parPI''' indepP indepQ interLeaved interLeavedToLabel P Q)
       
   parE' : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Node i B)  → (indepP indepQ : Label → Bool) → Choice
   parE' {i} {A} {B} P Q indepP indepQ = subset' (node2E P) (indepP ∘ node2Lab P) +'
                 subset' (node2E Q) (indepQ ∘ node2Lab Q)

   f :   {i : Size} →
         {A B : Set} →
         (P : Node i A) →
         (Q : Node i B) → {interLeaved : Label → Label → Bool}
         → ChoiceSet (node2E P ×' node2E Q) → Bool
   f {i} {A} {B} P Q {interLeaved} ( e₁ , e₂ ) = interLeaved (node2Lab Q e₂) (node2Lab P e₁)


   f₁ :  {i : Size} →
         {A B : Set} →
         (P : Node i A) →
         (Q : Node i B) → (interLeaved : Label → Label → Bool)
         → ChoiceSet (node2E P) × ChoiceSet (node2E Q) → Bool
   f₁ P Q interLeaved (e , e₁) = interLeaved (node2Lab P e) (node2Lab Q e₁) 


   parE₂ :  {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → Node i A → Node i B → (interLeaved : Label → Label → Bool) → Choice
   parE₂ indepP indepQ interLeaved interLeavedToLabel P Q e = subset' (node2E P ×' node2E Q) (f₁ P Q e)

   parE :  {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → Node i A → Node i B → Choice
   parE indepP indepQ interLeaved interLeavedToLabel P Q  = parE' P Q indepP indepQ  +' parE₂ indepP indepQ interLeaved interLeavedToLabel P Q interLeaved 
    

   parLab' : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
                                   → (P : Node i A) → (Q : Node i B)  → ChoiceSet (parE indepP indepQ interLeaved interLeavedToLabel P Q) → Label
   parLab' indepP indepQ interLeaved interLeavedToLabel P Q (inl (inl (sub e x))) = node2Lab P e
   parLab' indepP indepQ interLeaved interLeavedToLabel P Q (inl (inr (sub e x))) = node2Lab Q e
   parLab' indepP indepQ interLeaved interLeavedToLabel P Q (inr (sub (e , e₁) x)) = interLeavedToLabel (node2Lab P e) (node2Lab Q e₁) x
  
                                
   parPEE' : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) →  (P : Node i A) → (Q : Node i B)
                                   →   ChoiceSet (parE indepP indepQ interLeaved interLeavedToLabel P Q)  → ∞Processx i (A × B)                              
   forcex (parPEE' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel (thenode E Lab PE I PI) Q (inl (inl (sub e x)))) j = Parallelx'   j indepP indepQ interLeaved interLeavedToLabel A B (forcex (PE e) j) (node Q)
   forcex (parPEE' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P (thenode E Lab PE I PI) (inl (inr (sub e x)))) j = Parallelx'   j indepP indepQ interLeaved interLeavedToLabel A B (node P) (forcex (PE e) j)
   forcex (parPEE' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel (thenode E Lab PE I PI) (thenode E₁ Lab₁ PE₁ I₁ PI₁) (inr (sub    (e , e₁) x))) j = Parallelx' j indepP indepQ interLeaved interLeavedToLabel A B (forcex (PE e) j) (forcex (PE₁ e₁) j)


   I'' :  {i : Size} → {A B : Set} → Node i A →  Node i B → Choice
   I''  P Q =  (node2I P)  +'  (node2I Q)

   parPI'toP : (i : Size) → (j : Size< i) → (A B : Set)  → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Node i A) → (Q : Node i B)  
                  → ChoiceSet (I'' P Q) →  Processx j A
   parPI'toP i j A B indepP indepQ interLeaved interLeavedToLabel P Q (inl x) = forcex (node2PI P x) j
   parPI'toP i j A B indepP indepQ interLeaved interLeavedToLabel P Q (inr x) = node P

   parPI'toQ :  (i : Size) → (j : Size< i) → (A B : Set)  → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Node i A) → (Q : Node i B)  
                  → ChoiceSet (I'' P Q) →  Processx j B
   parPI'toQ i j A B indepP indepQ interLeaved interLeavedToLabel P Q (inl x) = node Q
   parPI'toQ i j A B indepP indepQ interLeaved interLeavedToLabel P Q (inr x) = forcex (node2PI Q x) j


   parPI'' : {i : Size} 
             → {A B : Set}  
             → (indepP indepQ : Label → Bool)
             → (interLeaved : Label → Label → Bool)
             → (interLeavedToLabel : (PLab QLab : Label) → True (interLeaved PLab QLab) → Label) 
             → (P : Node i A) → (Q : Node i B)  
             → ChoiceSet (I'' P Q) 
             →  ∞Processx i (A × B)
   forcex (parPI'' {i}  {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q x) j 
          = Parallelx' j indepP indepQ interLeaved interLeavedToLabel A B 
                       (parPI'toP i j A B indepP indepQ interLeaved interLeavedToLabel P Q x) 
                       (parPI'toQ i j A B indepP indepQ interLeaved interLeavedToLabel P Q x)


   parPI' : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Node i A) → (Q : Node i B) →  ChoiceSet (I'' P Q) → ∞Processx i (A × B)
   forcex (parPI' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q (inl x)) j = Parallelx' j indepP indepQ interLeaved interLeavedToLabel A B (forcex (node2PI P x) j)  (node Q)
   forcex (parPI' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q (inr x)) j = Parallelx' j indepP indepQ interLeaved interLeavedToLabel A B  (node P) (forcex (node2PI Q x) j)



   parPI''' : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Node i A) → (Q : Node i B) →  ChoiceSet (I'' P Q) → ∞Processx i (A × B)
   parPI''' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q (inl x) 
                   = Parallelx i indepP indepQ interLeaved interLeavedToLabel A B (node2PI P x)   (delayx i (node Q))
   parPI''' {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q (inr x) 
                   = Parallelx i indepP indepQ interLeaved interLeavedToLabel A B  (delayx i (node P)) (node2PI Q x)



   ParNode₁ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
                                   → (P : Node i A) → (Q : Processx i B)  → Node i (A × B)
   ParNode₁ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q = thenode (parE₁ P (terminate Q)) (parLab₁ P Q) (parPE₁ indepP indepQ interLeaved interLeavedToLabel P Q) (parI₁ P (terminate Q)) (parPI₁ indepP indepQ interLeaved interLeavedToLabel P Q)

   parE₁ : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Processx i B) → Choice
   parE₁ {i} {A} {B}  P Q = node2E P

   parLab₁ : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Processx i B) → ChoiceSet (parE₁ P (terminate Q)) → Label
   parLab₁ P Q e = node2Lab P e 
  
   parPE₁ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Node i A) → (Q : Processx i B)
                                   → ChoiceSet (parE₁ P (terminate Q)) → ∞Processx i (A × B)
   parPE₁ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q  x  = Parallelx i indepP indepQ interLeaved interLeavedToLabel A B (delayx i (node P)) (delayx i  Q)

   parI₁ : {i : Size} → {A B : Set} → (P : Node i A) → (Q : Processx i B) → Choice
   parI₁ {i} {A} {B}  P Q = node2I P




   parPI₁ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Node i A) → (Q : Processx i B)
                                   → ChoiceSet (parI₁ P (terminate Q)) → ∞Processx i (A × B)
   parPI₁ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q x  = Parallelx i indepP indepQ interLeaved interLeavedToLabel A B (delayx i (node P)) (delayx i  Q)




   ParNode₂ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
                                   → (P : Processx i A) → (Q : Node i B)  → Node i (A × B)
   ParNode₂ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q = thenode (parE'₂ (terminate P) Q) (parLab₂ P Q) (parPE₂ indepP indepQ interLeaved interLeavedToLabel P Q) (parI₂ (terminate P) Q) (parPI₂ indepP indepQ interLeaved interLeavedToLabel P Q)

   parE'₂ : {i : Size} → {A B : Set} → (P : Processx i A) → (Q : Node i B) → Choice
   parE'₂ {i} {A} {B}  P Q = node2E Q

   parLab₂ : {i : Size} → {A B : Set} → (P : Processx i A) → (Q : Node i B) → ChoiceSet (parE'₂ (terminate P) Q) → Label
   parLab₂ P Q e = node2Lab Q e 
  
   parPE₂ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Processx i A) → (Q : Node i B)
                                   → ChoiceSet (parE'₂ (terminate P)  Q) → ∞Processx i (A × B)
   parPE₂ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q  x  = Parallelx i indepP indepQ interLeaved interLeavedToLabel A B  (delayx i P) (delayx i (node Q))

   parI₂ : {i : Size} → {A B : Set} → (P : Processx i A) → (Q : Node i B) → Choice
   parI₂ {i} {A} {B}  P Q = node2I Q




   parPI₂ : {i : Size} → {A B : Set} → (indepP indepQ : Label → Bool)
                                   → (interLeaved : Label → Label → Bool)
                                   → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label) → (P : Processx i A) → (Q : Node i B)
                                   → ChoiceSet (parI₂ (terminate P) Q) → ∞Processx i (A × B)
   parPI₂ {i} {A} {B} indepP indepQ interLeaved interLeavedToLabel P Q x  = Parallelx i indepP indepQ interLeaved interLeavedToLabel A B (delayx i P) (delayx i (node Q))


parallelx : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → (A B : Set)
          → ∞Processx i A
          → ∞Processx i B
          → ∞Processx i (A × B)

parallelx = Parallelx _








parallelx' : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)          
          → (A B : Set)
          → Processx i A
          → Processx i B
          → Processx i (A × B)

parallelx'  =  Parallelx' _



postulate eqLabel : Label → Label → Bool

EqLabel : Label → Label → Set
EqLabel l₁ l₂ = True (eqLabel l₁ l₂)

eqLabelSwap : Label → Label → Bool
eqLabelSwap l₁ l₂ = eqLabel l₂ l₁

postulate symEqLabel  : (l l' : Label) → EqLabel l l' → EqLabel l' l
postulate eqLabelIsEq : (l l' : Label) → EqLabel l l' → l == l'


lab2ff : Label → Bool
lab2ff l = ff

chooseLab₁ : (l₁ l₂ : Label) → EqLabel l₁ l₂ → Label
chooseLab₁ l₁ l₂ p = l₁

chooseLab₂ : (l₁ l₂ : Label) → EqLabel l₂ l₁ → Label
chooseLab₂ l₁ l₂ p = l₂

{-
-------------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------------------------------------------------------

mutual
 refParallel : (i : Size) → {A B : Set} → (P : ∞Processx i A) →  (Q : ∞Processx i B) 
            → Refinementx i {A × B} {B × A} 
               ( Parallelx i lab2ff lab2ff eqLabel     chooseLab₁ A B P Q)
               ( Parallelx i lab2ff lab2ff eqLabelSwap chooseLab₂ B A Q P)
 forcex' (refParallel i P Q l x) j  = refParallel' j (forcex P j) (forcex Q j) l (forcex' x j) 

 refParallel' : (j : Size) → {A B : Set} → (P : Processx j A) →  (Q : Processx j B) 
            → Refinementx' j {A × B} {B × A} 
               (Parallelx' j lab2ff lab2ff eqLabel chooseLab₁ A B P Q)
               (Parallelx' j lab2ff lab2ff eqLabelSwap chooseLab₂ B A Q P)
 refParallel' i (node P) (node Q) .[] empty = empty
-}{-
_[_||_||_]_ : {i : Size}
          →  {!!}   →  {!!}
          → {!!}
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (eqLabel PLab QLab)
                                   → Label)       
           →  {A : Set} → {B : Set}
          → ∞Processx i  A   
          → ∞Processx i B
          → ∞Processx i (A × B)

_[_||_||_]_ = {! parallelx!}

-}
{-
_□_ : {i : Size} →  {A : Set} → {B : Set} → ∞Processx i  A  → ∞Processx i B → ∞Processx i ((A + B) + (A × B)) 
_□_ = extChx _ 

_□'_ : {i : Size} → {A : Set} → {B : Set} → Processx i  A  →  Processx i B → Processx i ((A + B) + (A × B))
_□'_ = extChx' _


infixl 10 _□_ 
infixl 10 _□'_ 
-}
