module parallel where 
 

open import Data.Bool renaming (T to True)
open import Data.Sum
open import Data.String
open import Size 
open import process 
open Process∞
open Process+
open import label
open import auxData
open import dataAuxFunction
open import choiceSetU
open import renamingResult

ParallelStr : (indepP indepQ : Label → Bool)
             → (interLeaved : Label → Label → Bool)
             → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
             →  String → String → String
ParallelStr indepP indepQ interLeaved interLeavedToLabel s s' = "Defined Later"

mutual
   Parallel∞ : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → {c₀ c₁ : Choice}
          → Process∞ i c₀
          → Process∞ i c₁
          → Process∞ i (c₀ ×' c₁)
   forcep (Parallel∞ indepP indepQ interLeaved interLeavedToLabel P Q)  
        = Parallel indepP indepQ interLeaved interLeavedToLabel (forcep P) 
                   (forcep Q)
   Str∞  (Parallel∞ indepP indepQ interLeaved interLeavedToLabel P Q) 
        = ParallelStr indepP indepQ interLeaved interLeavedToLabel (Str∞ P) (Str∞ Q) 

   Parallel : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → {c₀ c₁ : Choice}
          → Process i c₀
          → Process i c₁
          → Process i (c₀ ×' c₁)
   Parallel indepP indepQ interLeaved interLeavedToLabel (node p) (node q) =
                                     node (Parallel+ indepP indepQ interLeaved interLeavedToLabel p q)
   Parallel indepP indepQ interLeaved interLeavedToLabel (terminate a) Q = fmap (λ b → (a ,, b)) Q
   Parallel indepP indepQ interLeaved interLeavedToLabel P (terminate b) = fmap (λ a → (a ,, b)) P

   Parallel∞+ : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → {c₀ c₁ : Choice}
          → Process∞ i c₀
          → Process+ i c₁
          → Process∞ i (c₀ ×' c₁)

   forcep (Parallel∞+ indepP indepQ interLeaved interLeavedToLabel P Q) = node (Parallelp+ indepP indepQ interLeaved interLeavedToLabel  (forcep P) Q)
   Str∞  (Parallel∞+ indepP indepQ interLeaved interLeavedToLabel P Q) 
        = ParallelStr indepP indepQ interLeaved interLeavedToLabel (Str∞ P) (Str+ Q)  

   Parallel+∞ : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → {c₀ c₁ : Choice}
          → Process+ i c₀
          → Process∞ i c₁
          → Process∞ i (c₀ ×' c₁)

   forcep (Parallel+∞ indepP indepQ interLeaved interLeavedToLabel P Q) = node (Parallel+p indepP indepQ interLeaved interLeavedToLabel P  (forcep Q))
   Str∞  (Parallel+∞ indepP indepQ interLeaved interLeavedToLabel P Q) 
        = ParallelStr indepP indepQ interLeaved interLeavedToLabel (Str+ P) (Str∞ Q)  

   Parallelp+ : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → {c₀ c₁ : Choice}
          → Process i c₀
          → Process+ i c₁
          → Process+ i (c₀ ×' c₁)

   Parallelp+ indepP indepQ interLeaved interLeavedToLabel (terminate a) Q = fmap+ (λ b → (a ,, b)) Q
   Parallelp+ indepP indepQ interLeaved interLeavedToLabel (node p) Q =  Parallel+ indepP indepQ interLeaved interLeavedToLabel p Q

   Parallel+p : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → {c₀ c₁ : Choice}
          → Process+ i c₀
          → Process  i c₁
          → Process+ i (c₀ ×' c₁)

   Parallel+p indepP indepQ interLeaved interLeavedToLabel P (terminate b) = fmap+ (λ a → (a ,, b)) P
   Parallel+p indepP indepQ interLeaved interLeavedToLabel P (node q) = Parallel+ indepP indepQ interLeaved interLeavedToLabel P q


   Parallel+ : {i : Size}
          → (indepP indepQ : Label → Bool)
          → (interLeaved : Label → Label → Bool)
          → (interLeavedToLabel : (PLab QLab : Label) 
                                   → True (interLeaved PLab QLab)
                                   → Label)
          → {c₀ c₁ : Choice}
          → Process+ i c₀
          → Process+ i c₁
          → Process+ i (c₀ ×' c₁)
   E    (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q)   = (subset' (E P) (indepP ∘ (Lab P)) 
                                                                         ⊎' subset' (E Q) (indepQ ∘ (Lab Q)) )
                                                                         ⊎' subset' (E P ×' E Q) 
                                                                             (λ {(e₁ ,, e₂) → interLeaved (Lab P e₁) (Lab Q e₂)})
   Lab (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q) (inj₁ (inj₁ (sub c tc))) = Lab P c
   Lab (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q) (inj₁ (inj₂ (sub c tc))) = Lab Q c
   Lab (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q) (inj₂ (sub (c₁ ,, c₂) tcc₁)) = interLeavedToLabel (Lab P c₁) (Lab Q c₂) tcc₁
   PE (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q) (inj₁ (inj₁ (sub c tc))) = Parallel∞+ indepP indepQ interLeaved interLeavedToLabel (PE P c) Q
   PE (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q) (inj₁ (inj₂ (sub c tc))) = Parallel+∞ indepP indepQ interLeaved interLeavedToLabel P (PE Q c) 
   PE (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q) (inj₂ (sub (c₁ ,, c₂) tcc₁)) = Parallel∞ indepP indepQ interLeaved interLeavedToLabel (PE P c₁) (PE Q c₂)
   I    (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q)   = I P ⊎' I Q
   PI (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q) (inj₁ c) = Parallel∞+ indepP indepQ interLeaved interLeavedToLabel (PI P c) Q
   PI (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q) (inj₂ c) = Parallel+∞ indepP indepQ interLeaved interLeavedToLabel P (PI Q c) 
   T    (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q)   = T P ×' T Q 
   PT   (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q) (c ,, c₁) = PT P c ,, PT Q c₁
   Str+  (Parallel+ indepP indepQ interLeaved interLeavedToLabel P Q)   = 
       ParallelStr indepP indepQ interLeaved interLeavedToLabel (Str+ P) (Str+ Q) 
  
