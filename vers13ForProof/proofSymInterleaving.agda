module proofSymInterleaving where 

open import process 
open import indTr
open Process'
open Process
open Process∞
open Tr∞
open import Size
open import choiceSetU
open import auxData
open import Data.Maybe
open import Data.Product renaming ( _×_ to _×''_)
open import interleave
open import Data.List
open import Data.Sum
open import label
open import renamingResult

--open import Data.Product ×

swap⊎ : {c₀ c₁ : Choice} → ChoiceSet (c₀ ⊎' c₁) → ChoiceSet (c₁ ⊎' c₀)
swap⊎ (inj₁ x) = inj₂ x
swap⊎ (inj₂ y) = inj₁ y

swap× : {c₀ c₁ : Choice} → ChoiceSet (c₀ ×' c₁) → ChoiceSet (c₁ ×' c₀)
swap× (x₀ ,, x₁) = (x₁ ,, x₀)

mutual 
 Sym||| : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process i c₀)
         → (Q : Process i c₁)
         → Ref (P ||| Q) (fmap swap× (Q ||| P))
 Sym||| P Q .[] .nothing empty = empty
 Sym||| P Q .(Lab P x ∷ l) m (extchoice l .m (inj₁ x) x₁) = extchoice l m (inj₂ x) (Sym|||∞p (PE P x) Q l m x₁)
 Sym||| P Q .(Lab Q y ∷ l) m (extchoice l .m (inj₂ y) x₁) = extchoice l m (inj₁ y) (Sym|||p∞ P (PE Q y) l m x₁) 
 Sym||| P Q l m (intchoice .l .m (inj₁ x) x₁)             = intchoice l m (inj₂ x) (Sym|||∞p (PI P x) Q l m x₁)
 Sym||| P Q l m (intchoice .l .m (inj₂ y) x₁)             = intchoice l m (inj₁ y) (Sym|||p∞ P (PI Q y) l m x₁)
 Sym||| P Q .[] .(just (PT P x ,, PT Q x₁)) (terchoice (x ,, x₁)) = terchoice (x₁ ,, x)


 Sym|||p∞  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process i c₀)
         → (Q : Process∞  i c₁)
         → Ref∞ {i}  (P |||p∞ Q) (fmap∞  swap× {i} (Q |||∞p P))
 forcet (Sym|||p∞ P Q l m x) = Sym||| P (forcep Q) l m (forcet x)


 Sym|||∞p  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process∞  i c₀)
         → (Q : Process  i c₁)
         → Ref∞ {i}  (P |||∞p Q) (fmap∞  swap× {i} (Q |||p∞ P))
 forcet (Sym|||∞p P Q l m x)  = Sym||| (forcep P) Q l m (forcet x)



mutual 
 Sym|||R : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process i c₀)
         → (Q : Process i c₁)
         → Ref (fmap swap× (Q ||| P)) (P ||| Q)
 Sym|||R Q P .[] .nothing empty = empty
 Sym|||R Q P .(Lab P x ∷ l) m (extchoice l .m (inj₁ x) x₁) = extchoice l m (inj₂ x) (Sym|||Rp∞ Q (PE P x) l m x₁)
 Sym|||R Q P .(Lab Q y ∷ l) m (extchoice l .m (inj₂ y) x₁) = extchoice l m (inj₁ y) (Sym|||R∞p (PE Q y) P l m x₁)
 Sym|||R Q P l m (intchoice .l .m (inj₁ x) x₁)             = intchoice l m (inj₂ x) (Sym|||Rp∞ Q (PI P x) l m x₁)
 Sym|||R Q P l m (intchoice .l .m (inj₂ y) x₁)             = intchoice l m (inj₁ y) (Sym|||R∞p (PI Q y) P l m x₁)
 Sym|||R Q P .[] .(just (PT Q x₁ ,, PT P x)) (terchoice (x ,, x₁)) =  terchoice (x₁ ,, x)

 Sym|||Rp∞  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process i c₀)
         → (Q : Process∞  i c₁)
         → Ref∞ {i} (fmap∞  swap× {i} (Q |||∞p P)) (P |||p∞ Q) 
 forcet (Sym|||Rp∞ Q P l m x) = Sym|||R Q (forcep P) l m ((forcet x))


 Sym|||R∞p  : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process∞ i c₀)
         → (Q : Process  i c₁)
         → Ref∞ {i} (fmap∞  swap× {i} (Q |||p∞ P)) (P |||∞p Q)
 forcet (Sym|||R∞p Q P l m x)  = Sym|||R (forcep Q) P l m ((forcet x))


|||≡ : {i : Size} → {c₀ c₁ : Choice}
         → (P : Process i c₀)
         → (Q : Process i c₁)
         → Ref (fmap swap× (Q ||| P)) (P ||| Q)
         → Ref  (P ||| Q) (fmap swap× (Q ||| P))
         → (P ||| Q) ≡ (fmap swap×  ((Q ||| P)))
|||≡ P Q r₁ r₂ = r₂ , r₁



{-
swapTr : {c₀ c₁ c₂ : Choice} → ChoiceSet ((c₀ ×' c₁) ×' c₂) → ChoiceSet (c₀ ×' (c₁ ×' c₂))
swapTr {c₀} {c₁} {c₂} ((x ,, x₁) ,, x₂) = (x ,, (x₁ ,, x₂))

swapTr' : {c₀ c₁ c₂ : Choice} → ChoiceSet (c₀ ×' (c₁ ×' c₂))  → ChoiceSet ((c₀ ×' c₁) ×' c₂)
swapTr' {c₀} {c₁} {c₂}  (x ,, (x₁ ,, x₂)) = ((x ,, x₁) ,, x₂)



mutual 
 Tra|||' : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process i c₀)
         → (Q : Process i c₁)
         → (Z : Process i c₂)
         → Ref ((P ||| Q) ||| Z) (fmap swapTr' (P |||( Q ||| Z)))
 
 Tra|||'  P Q Z .[] .nothing empty = empty
 Tra|||'  P Q Z .(Lab P x ∷ l) m (extchoice l .m (inj₁ (inj₁ x)) x₁) = extchoice l m (inj₁ x) (Tr|||p∞∞'' (PE P x) Q Z l m x₁)
 Tra|||'  P Q Z .(Lab Q y ∷ l) m (extchoice l .m (inj₁ (inj₂ y)) x₁) = extchoice l m (inj₂ (inj₁ y)) {!Tr|||∞p∞'!}
 Tra|||'  P Q Z .(Lab Z y ∷ l) m (extchoice l .m (inj₂ y) x₁) = extchoice l m  (inj₂ (inj₂ y)) {!Tr|||∞p∞'!}
 Tra|||'  P Q Z l m (intchoice .l .m (inj₁ (inj₁ x)) x₁) = intchoice l m ((inj₁ x)) {!!} --(Tr|||p∞∞' ? ? ? l m ?) 
 Tra|||'  P Q Z l m (intchoice .l .m (inj₁ (inj₂ y)) x₁) = intchoice l m ((inj₂ (inj₁ y))) {!Tr|||∞p∞'!}
 Tra|||'  P Q Z l m (intchoice .l .m (inj₂ y) x₁) = intchoice l m ( (inj₂ (inj₂ y))) {!!}
 Tra|||'  P Q Z .[] .(just ((PT P x ,, PT Q x₁) ,, PT Z x₂)) (terchoice ((x ,, x₁) ,, x₂)) = (terchoice (x ,, (x₁ ,, x₂))) 



 Tr|||p∞∞'  : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process   i c₀)
         → (Q : Process∞  i c₁)
         → (Z : Process∞  i c₂)
         → Ref∞ (((P |||p∞ Q) |||∞ Z)) (fmap∞ swapTr' ( ((P |||p∞ (Q |||∞ Z))) ))
 forcet (Tr|||p∞∞' P Q Z l m x) =  Tra|||' P (forcep Q) (forcep Z) l m ( ((forcet x)))



 Tr|||p∞∞n'  : {i : Size} → {j : Size< i} → {c₀ c₁ c₂ : Choice}
         → {P : Process∞ i c₀}
         → {Q : Process  i c₁}
         → {Z : Process  i c₂}
         → Ref∞ (((forcep {i} P |||p∞ delay Q) |||∞ delay Z)) (fmap∞ swapTr' ( ((forcep P |||p∞ (delay Q |||∞ delay Z))) ))
 forcet (Tr|||p∞∞n' {i} {j} {c₀} {c₁} {c₂} {P} {Q} {Z} l m x) = Tra|||' (forcep P) (forcep (delay Q)) (forcep (delay Z)) l m (forcet x)



 Tr|||∞p∞'  : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process∞   i c₀)
         → (Q : Process  i c₁)
         → (Z : Process∞  i c₂)
         → Ref∞ (((P |||∞p Q) |||∞ Z)) (fmap∞ swapTr' ( ((P |||∞ (Q |||p∞ Z))) ))
 forcet (Tr|||∞p∞' P Q Z l m x) = Tra|||' (forcep P) Q (forcep Z) l m (forcet x)


{-
 Tr|||p∞∞'  : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process   i c₀)
         → (Q : Process∞  i c₁)
         → (Z : Process∞  i c₂)
         → Ref∞ (((P |||p∞ (Q |||∞ Z)))) (fmap∞ swapTr (((P |||p∞ Q) |||∞ Z))) 
 forcet (Tr|||p∞∞' P Q Z l m x) = {!!} -- Tra|||' P (forcep Q) (forcep Z) l m ((forcet x))
-}


{-
-- 0  Tr∞ l m (fmap∞ swapTr' (PE P x |||∞p (Q ||| Z)))

 Tr|||p∞∞  : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process∞ i c₀)
         → (Q : Process  i c₁)
         → (Z : Process  i c₂)
         → Ref∞ {i} ( P |||∞ delay Q |||∞ delay Z) (fmap∞ swapTr' {i} ((P |||∞p (Q ||| Z))))  --((P |||∞p Q) ||| Z)
 Tr|||p∞∞ P Q Z l m x = {!Tra|||'!} -- Tra|||' P (forcep Q) (forcep Z) l m ((forcet x))
-}


-- Tr∞ l m (fmap∞ swapTr' (PE P x |||∞p (Q ||| Z)))

 Tr|||p∞∞''  : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process∞   i c₀)
         → (Q : Process    i c₁)
         → (Z : Process    i c₂)
         → Ref∞ ((( P |||∞p Q) |||∞p Z)) (fmap∞ swapTr' (((P |||∞p (Q ||| Z))))) 
 forcet (Tr|||p∞∞'' P Q Z l m x) = {!Tr|||p∞∞'''!} --Tra|||' (forcep P)  Q Z l m ((forcet x))





 Tr|||p∞∞'''  : {i : Size} → {j : Size< i} → {c₀ c₁ c₂ : Choice}
         → (P : Process∞ i c₀)
         → (Q : Process i c₁)
         → (Z : Process i c₂)
         → (m   : Maybe ((ChoiceSet .c₀ × ChoiceSet .c₁) × ChoiceSet .c₂))
         → (l   : List Label)
         → (x   : Tr∞ l m ((P |||∞p Q) |||∞p Z))
         → Tr l m (fmap swapTr' (forcep P ||| (Q ||| Z)))
         
 forcet (Tr|||p∞∞''' P Q Z l m x) = {!Tr|||p∞∞!} --Tra|||' (forcep P)  Q Z l m ((forcet x))

{-
Goal:
————————————————————————————————————————————————————————————

-}


{-
 Goal: Tr l m (fmap swapTr' (forcep P ||| (Q ||| Z)))
————————————————————————————————————————————————————————————
.j  : Size< .i
x   : Tr∞ l m ((P |||∞p Q) |||∞p Z)
m   : Maybe ((ChoiceSet .c₀ × ChoiceSet .c₁) × ChoiceSet .c₂)
l   : List Label
Z   : Process .i .c₂
Q   : Process .i .c₁
P   : Process∞ .i .c₀
.c₂ : Choice
.c₁ : Choice
.c₀ : Choice
.i  : Size
-}





{-
 Tr|||p∞∞''  : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process∞   i c₀)
         → (Q : Process    i c₁)
         → (Z : Process    i c₂)
         → Ref∞ {i} (( P |||∞ delay Q |||∞ delay Z)) (fmap∞ swapTr' {i} ((P |||∞p (Q ||| Z))))
 forcet (Tr|||p∞∞'' P Q Z l m x) = {!Tra|||'!} --Tra|||' (forcep P)  Q Z l m ((forcet x))



-}


 Tr|||p∞∞  : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process   i c₀)
         → (Q : Process∞  i c₁)
         → (Z : Process∞  i c₂)
         → Ref∞ {i} ((P |||p∞ Q) |||∞ Z) (fmap∞ swapTr' {i} ((P |||p∞ (Q |||∞ Z))))
 forcet (Tr|||p∞∞ P Q Z l m x) = Tra|||' P (forcep Q) (forcep Z) l m ((forcet x))


 Tr|||∞p∞  : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process∞   i c₀)
         → (Q : Process  i c₁)
         → (Z : Process∞  i c₂)
         → Ref∞ {i} ((P |||∞p Q) |||∞ Z) (fmap∞ swapTr' {i} ((P |||∞ (Q |||p∞ Z))))
 forcet (Tr|||∞p∞ P Q Z l m x) = Tra|||' (forcep P)  Q (forcep Z) l m ((forcet x))



 Tr|||∞∞p  : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process∞ i c₀)
         → (Q : Process∞ i c₁)
         → (Z : Process  i c₂)
         → Ref∞ {i} ((P |||∞ Q) |||∞p Z) (fmap∞ swapTr' {i} ((P |||∞ (Q |||∞p Z))))
 forcet (Tr|||∞∞p P Q Z l m x) =   Tra|||' (forcep P)  (forcep Q) Z l m ((forcet x))





{-
mutual 
 Tra||| : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process i c₀)
         → (Q : Process i c₁)
         → (Z : Process i c₂) 
         → RefTr ((P ||| Q) ||| Z) (P |||( Q ||| Z)) 
 
 Tra||| P Q Z .[] .nothing (just (x ,, (x₁ ,, x₂))) empty =                                                 {!!}
 Tra||| P Q Z .[] .nothing nothing empty = empty
 Tra||| P Q Z .(Lab P x ∷ l) m m₁ (extchoice l .m (inj₁ (inj₁ x)) x₁) = extchoice l m₁ ((inj₁ x))           {!!}
 Tra||| P Q Z .(Lab Q y ∷ l) m m₁ (extchoice l .m (inj₁ (inj₂ y)) x₁) = extchoice l m₁ (inj₂ (inj₁ y))      {!!}
 Tra||| P Q Z .(Lab Z y ∷ l) m m₁ (extchoice l .m (inj₂ y) x₁)        = extchoice l m₁ ((inj₂ (inj₂ y)))    {!!}
 Tra||| P Q Z l m m₁ (intchoice .l .m (inj₁ (inj₁ x)) x₁) = intchoice l m₁ ((inj₁ x))                        {!!}
 Tra||| P Q Z l m m₁ (intchoice .l .m (inj₁ (inj₂ y)) x₁) = intchoice l m₁ (inj₂ (inj₁ y))                   {!!}
 Tra||| P Q Z l m m₁ (intchoice .l .m (inj₂ y) x₁) = intchoice l m₁ (inj₂ (inj₂ y))                          {!!}
 Tra||| P Q Z .[] .(just ((PT P x ,, PT Q x₁) ,, PT Z x₂)) (just (x₃ ,, x₄)) (terchoice ((x ,, x₁) ,, x₂)) = {!!}
 Tra||| P Q Z .[] .(just ((PT P x ,, PT Q x₁) ,, PT Z x₂)) nothing (terchoice ((x ,, x₁) ,, x₂)) = empty
-}

{-
Goal: Tr∞ l m (fmap∞ swapTr' (PE P x |||∞p (Q ||| Z)))
————————————————————————————————————————————————————————————
x₁  : Tr∞ l m ((PE P x |||∞p Q) |||∞p Z)
m   : Maybe ((ChoiceSet .c₀ × ChoiceSet .c₁) × ChoiceSet .c₂)
x   : ChoiceSet (E P)
l   : List Label
Z   : Process .i .c₂
Q   : Process .i .c₁
P   : Process .i .c₀
.i  : Size
.c₂ : Choice
.c₁ : Choice
.c₀ : Choice
-}


{-
 Tr|||p∞∞''  : {i : Size} → {c₀ c₁ c₂ : Choice}
         → (P : Process   i c₀)
         → (Q : Process∞  i c₁)
         → (Z : Process∞  i c₂)
         → Ref∞ {i} ((P |||p∞ Q) |||∞ Z) (fmap∞ swapTr' {i} ((P |||p∞ (Q |||∞ Z))))
 forcet (Tr|||p∞∞'' P Q Z l m x) = Tra|||' P (forcep Q) (forcep Z) l m ((forcet x))
-}
-}
