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

boolEq : {A : Set}(eqA : A → A → Bool)(l l' : List A) →  Bool
boolEq eqA [] [] = true
boolEq eqA [] (x ∷ l') = false
boolEq eqA (x ∷ l) [] = false
boolEq eqA (a ∷ l) (a₁ ∷ l') = eqA a a₁ ∧ boolEq eqA l l'
