module labelEq where

open import label
open import Data.Bool

_==l_ : Label → Label → Bool
laba ==l laba = true
labb ==l labb = true
labc ==l labc = true
_    ==l _    = false





