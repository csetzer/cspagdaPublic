module labelEq where

open import label
open import Data.Bool
open import Data.Bool.Base renaming (T to T')
open import Data.Unit

_==l_ : Label → Label → Bool
laba ==l laba = true
labb ==l labb = true
labc ==l labc = true
_    ==l _    = false


refl==l : {l : Label} → T' (l ==l l)
refl==l {laba} = tt
refl==l {labb} = tt
refl==l {labc} = tt





