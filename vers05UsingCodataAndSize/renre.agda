module renre where
open import Size
open import pro
open ∞Process
open ∞Processx

------  Renaming the Result returned ----------


mutual 
  fmap : (i : Size) → {A B : Set} → (A → B) → ∞Process i A → ∞Process i B
  force (fmap i f x )  j = fmap' j f (force x j)

  fmap' :  (i : Size) → {A B : Set} → (A → B) → Process i A → Process i B  
  fmap' i f (node E Lab PE I PI) = node E Lab (λ x → fmap i f (PE x)) I (λ x → fmap i f (PI x))
  fmap' i f (terminate x) = terminate (f x)




------  Renaming the Result returned ----------


mutual 
  fmapx : (i : Size) → {A B : Set} → (A → B) → ∞Processx i A → ∞Processx i B
  forcex (fmapx i f x )  j = fmapx' j f (forcex x j)

  fmapx'' : (i : Size) → {A B : Set} → (A → B) → Node i A → Node i B  
  fmapx'' i f (thenode E Lab PE I PI) = thenode E Lab (λ x → fmapx i f (PE x)) I (λ x → fmapx i f (PI x))

  fmapx' :  (i : Size) → {A B : Set} → (A → B) → Processx i A → Processx i B  
  fmapx' i f (node P) = node (fmapx'' i f P)
  fmapx' i f (terminate x) = terminate (f x)




