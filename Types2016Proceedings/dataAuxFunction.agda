module dataAuxFunction where

open import auxData
open import Data.Bool
open import Data.Nat
open import Agda.Builtin.Nat renaming (_<_ to _<N_; _==_ to _==N_)
open import Data.Fin renaming (_+_ to _+,_;_<_ to _<F_)
open import Data.Char.Unsafe renaming (_==_ to _==?_)
open import Data.Char hiding (isDigit)
open import Data.Maybe
open import Data.String.Unsafe renaming  (_==_ to _==strb)
open import Data.String renaming  (_++_ to _++s_)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List.Base renaming (map to mapL)
open import Data.Sum
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Product hiding ( _×_ )

¬ : Set → Set
¬ a = a → ⊥


¬b : Bool → Bool
¬b true = false
¬b false = true


tertiumNonDatur : (b : Bool) → T b ⊎ T (¬b b)
tertiumNonDatur true = inj₁ tt
tertiumNonDatur false = inj₂ tt

transfer : {A : Set} → (C : A → Set) → (a a' : A) → a == a' → C a → C a'
transfer C a .a refl c = c

projSubset : {A : Set} → {f : A → Bool}  → subset A f → A
projSubset (sub a x) = a


_∘_ : {A B C : Set} →  (B →  C) →  (A →  B) →  A →  C
(f ∘ g) a = f ( g a )

infixr 9 _∘_


π₀ : {A B : Set} →  A × B →  A
π₀ ( a ,, b) = a

π₁ : {A B : Set} →  A × B →  B
π₁ ( a ,, b) = b


efq : {A : Set} → Fin 0 →  A
efq ()



isDigit : Char → Maybe ℕ
isDigit '0' = just 0
isDigit '1' = just 1
isDigit '2' = just 2
isDigit '3' = just 3
isDigit '4' = just 4
isDigit '5' = just 5
isDigit '6' = just 6
isDigit '7' = just 7
isDigit '8' = just 8
isDigit '9' = just 9
isDigit _   = nothing

attach : Maybe ℕ → ℕ → ℕ
attach nothing  n = n
attach (just m) n = 10 * m + n

Quote : List Char → Maybe (List ℕ)
Quote xs = parse xs nothing []
  where
    parse : List Char → Maybe ℕ → List ℕ → Maybe (List ℕ)
    parse []         nothing  ns = just ns
    parse []         (just n) ns = just (n ∷ ns)
    parse (hd ∷  tl)  m        ns with isDigit hd
    ... | nothing = nothing
    ... | just n  = parse tl (just (attach m n)) ns

stringListToℕ : String → Maybe (List ℕ)
stringListToℕ xs with Quote (toList xs)
... | nothing = nothing
... | just ns = just (reverse ns)


listℕtoℕ'   : List ℕ → ℕ
listℕtoℕ' [] = 0
listℕtoℕ' (n ∷ l) = listℕtoℕ' l * 10 + n

listℕtoℕ   : List ℕ → ℕ
listℕtoℕ l = listℕtoℕ' (reverse l)

stringToMaybeℕ : String → Maybe ℕ
stringToMaybeℕ s  with  (stringListToℕ s)
stringToMaybeℕ s | just l = just (listℕtoℕ l)
stringToMaybeℕ s | nothing = nothing

<ℕboolTo< : {n m : ℕ } →   T (n <N m) → n < m
<ℕboolTo< {zero} {zero} ()
<ℕboolTo< {zero} {suc m} p = s≤s z≤n
<ℕboolTo< {suc n} {zero} ()
<ℕboolTo< {suc n} {suc m} p = s≤s (<ℕboolTo< {n} {m} p)


sumFin : (n : ℕ) → (Fin n → ℕ) → ℕ
sumFin zero _ = 0
sumFin (suc n) f = f zero + sumFin n (f ∘ suc)

prodFin : (n : ℕ) → (Fin n → ℕ) → ℕ
prodFin zero _ = 1
prodFin (suc n) f = f zero * sumFin n (f ∘ suc)



embed : {n : ℕ} → Fin n → Fin (suc n)
embed zero = zero
embed (suc m) = suc (embed m)

last : {n : ℕ} → Fin (suc n )
last {zero} = zero
last {suc n} = suc (last {n})

fin2OptionAux : {n : ℕ} →  String × Fin n → String × Fin (suc n)
fin2OptionAux (str ,, k) = (str ,, embed  k)

fin2Option' : (n : ℕ)  → List (String × Fin n)
fin2Option' zero = []
fin2Option' (suc n) = (showℕ n ,, last ) ∷ mapL fin2OptionAux (fin2Option' n)

fin2Option : (n : ℕ)  → List (String × Fin n)
fin2Option n = reverse (fin2Option' n)


fin2Option0' : (n : ℕ)  → List (Fin n)
fin2Option0' zero = []
fin2Option0' (suc n) = last  ∷ mapL embed (fin2Option0' n)

fin2Option0 : (n : ℕ)  → List (Fin n)
fin2Option0 n = reverse (fin2Option0' n)
