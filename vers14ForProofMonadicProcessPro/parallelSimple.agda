module parallelSimple where 

-- version of parallel which is as in standard CSP
 

open import Data.Bool renaming (T to True)
open import Data.Sum
open import Data.String renaming (_++_ to _++s_)
open import Data.String.Base 
open import Size 
open import process 
open Process∞
open Process+
open import label
open import auxData
open import dataAuxFunction
open import choiceSetU
open import renamingResult
open import showLabelP
open import labelEq
open import restrict

_∖_ : {X : Set} → (A B : X → Bool) → X → Bool
(A ∖ B)  c  = A c ∧ (¬b (B c))

-- ∖   is input as \setminus

_[_]||Str[_]_ : String → (A  B : Label → Bool)
                                 → String  → String
s [ A ]||Str[ B ] t = s ++s "[" ++s labelBoolFunToString A ++s 
                             "]||["  ++s labelBoolFunToString A ++s 
                            "]"   ++s t 
                    

mutual
   _[_]||∞[_]_ : {i : Size} → {c₀ c₁ : Choice}
                   → Process∞ i c₀ 
                   → (A  B : Label → Bool)
                   → Process∞ i c₁  
                   → Process∞ i (c₀ ×' c₁)
   forcep ( P [ A ]||∞[ B ] Q ) = forcep P [ A ]||[    B ] forcep Q
   Str∞   ( P [ A ]||∞[ B ] Q ) = Str∞   P [ A ]||Str[ B ] Str∞ Q

   _[_]||[_]_ : {i : Size} → {c₀ c₁ : Choice}
                   → Process i c₀ 
                   → (A  B : Label → Bool)
                   → Process i c₁  
                   → Process i (c₀ ×' c₁)
   node P      [ A ]||[ B ] node Q      = node (P [ A ]||+[ B ] Q)
   terminate a [ A ]||[ B ] Q           = fmap (λ b → (a ,, b)) 
                                           (Q ↾ (B ∖ A))
   P           [ A ]||[ B ] terminate b = fmap (λ a → (a ,, b))
                                           (P ↾ (A ∖ B))
                       

   _[_]||∞+[_]_ : {i : Size} → {c₀ c₁ : Choice}
                   → Process∞ i c₀ 
                   → (A  B : Label → Bool)
                   → Process+ i c₁  
                   → Process∞ i (c₀ ×' c₁)
   forcep (P [ A ]||∞+[ B ] Q)  = node (forcep P [ A ]||p+[ B ] Q)   
   Str∞   (P [ A ]||∞+[ B ] Q)  = Str∞   P [ A ]||Str[ B ] Str+ Q


   _[_]||+∞[_]_ : {i : Size} → {c₀ c₁ : Choice}
                   → Process+ i c₀ 
                   → (A  B : Label → Bool)
                   → Process∞ i c₁  
                   → Process∞ i (c₀ ×' c₁)
   forcep (P [ A ]||+∞[ B ] Q)  = node (P [ A ]||+p[  B ] forcep Q)  
   Str∞   (P [ A ]||+∞[ B ] Q)  = Str+  P [ A ]||Str[ B ] Str∞ Q


   _[_]||p+[_]_ : {i : Size} → {c₀ c₁ : Choice}
                   → Process i c₀ 
                   → (A  B : Label → Bool)
                   → Process+ i c₁  
                   → Process+ i (c₀ ×' c₁)
   (terminate a) [ A ]||p+[ B ] Q    = fmap+ (λ b → (a ,, b)) 
                                           (Q ↾+ (B ∖ A) )
   (node P)      [ A ]||p+[ B ] Q    = P [ A ]||+[ B ] Q
  


   _[_]||+p[_]_ : {i : Size} → {c₀ c₁ : Choice}
                   → Process+ i c₀ 
                   → (A  B : Label → Bool)
                   → Process i c₁  
                   → Process+ i (c₀ ×' c₁)
   P  [ A ]||+p[ B ] terminate b = fmap+ (λ a → (a ,, b)) 
                                    (P ↾+ (A ∖ B))
   P  [ A ]||+p[ B ] node Q      = P [ A ]||+[ B ] Q


   _[_]||+[_]_ : {i : Size} → {c₀ c₁ : Choice}
                  → Process+ i c₀ 
                  → (A  B : Label → Bool)
                  → Process+ i c₁  
                  → Process+ i (c₀ ×' c₁)
   E    (P [ A ]||+[ B ] Q)   =  subset' (E P) ((¬b ∘ A) ∘ (Lab P))
                             ⊎' (subset' (E Q) ((¬b ∘ B) ∘ (Lab Q))
                             ⊎' subset' (E P ×' E Q) (λ {(e₁ ,, e₂) 
                                        → Lab P e₁ ==l Lab Q e₂ ∧
                                           A (Lab P e₁)          ∧ 
                                           B (Lab Q e₂)}))                      
   Lab (P [ A ]||+[ B ] Q) (inj₁ (sub c p)) = Lab P c
   Lab (P [ A ]||+[ B ] Q) (inj₂ (inj₁ (sub c p))) = Lab Q c
   Lab (P [ A ]||+[ B ] Q) (inj₂ (inj₂ (sub (c₀ ,, c₁) p))) =  Lab P c₀ 
   PE (P [ A ]||+[ B ] Q) (inj₁ (sub c p)) =  PE P c [ A ]||∞+[ B ] Q 
   PE (P [ A ]||+[ B ] Q) (inj₂ (inj₁ (sub c p))) =  P [ A ]||+∞[ B ] PE Q c 
   PE (P [ A ]||+[ B ] Q) (inj₂ (inj₂ (sub (c₀ ,, c₁) p))) =  PE P c₀ [ A ]||∞[ B ] PE Q c₁  
   I    (P [ A ]||+[ B ] Q)   =  I P ⊎' I Q 
   PI (P [ A ]||+[ B ] Q) (inj₁ c) = PI P c [ A ]||∞+[ B ] Q 
   PI (P [ A ]||+[ B ] Q) (inj₂ c) =  P  [ A ]||+∞[ B ] PI Q c
   T    (P [ A ]||+[ B ] Q)   =  T P ×' T Q  
   PT (P [ A ]||+[ B ] Q) (c₀ ,, c₁) =  PT P c₀ ,, PT Q c₁ 
   Str+ (P [ A ]||+[ B ] Q)   = Str+ P [ A ]||Str[ B ]  Str+ Q





