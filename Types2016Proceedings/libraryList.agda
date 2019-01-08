module libraryList where


open import Data.Bool
open import Data.List


mutual
  filterBool : {A : Set}(f : A → Bool)(l : List A) → List A
  filterBool f [] = []
  filterBool f (x ∷ l) = filterBoolAux f x (f x) l

  filterBoolAux : {A : Set}(f : A → Bool)(a : A)(b : Bool)(l : List A) → List A
  filterBoolAux f a false l = filterBool f l
  filterBoolAux f a true l = a ∷ filterBool f l
