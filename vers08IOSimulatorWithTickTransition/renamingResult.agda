module renamingResult where

open import process
open Process∞
open Process+
open import Size
open import Data.String renaming (_++_ to _++s_)

mutual

  -- needs extra argument which is a name given by the user for the function

  fmap∞ : {A B : Set} → (f : A → B) → (i : Size) → Process∞ i A → Process∞ i B  
  forcep (fmap∞  {A} {B} f i P) j = fmap f j (forcep P j)

  fmap  : {A B : Set} → (f : A → B) → (i : Size) → Process i A  → Process i B  
  fmap f i (terminate a) = terminate (f a)
  fmap f i (node P) = node (fmap+ f i P)

  fmap+ : {A B : Set} → (f : A → B) → (i : Size) → Process+ i A → Process+ i B 
  E   (fmap+  {A} {B} f i P)   = E P
  Lab (fmap+  {A} {B} f i P) c = Lab P c
  PE  (fmap+  {A} {B} f i P) c = fmap∞ f i (PE P c)
  I   (fmap+  {A} {B} f i P)   = I P
  PI  (fmap+  {A} {B} f i P) c = fmap∞ f i (PI P c)
  T   (fmap+  {A} {B} f i P)   = T P
  PT  (fmap+  {A} {B} f i P) c = f (PT P c)
  Str (fmap+  {A} {B} f i P)   = "fmap" ++s Str P  -- "fmap(" ++s  fToStr ++s "," ++s Str P ++s ")"


  fmapi : {A B : Set} → (f : A → B) → {i : Size} → Process i A → Process i B  
  fmapi f {i} P = fmap f i P

  fmap+i : {A B : Set} → (f : A → B) → {i : Size} → Process+ i A → Process+ i B 
  fmap+i f {i} P = fmap+ f i P

  fmap∞i : {A B : Set} → (f : A → B) → {i : Size} → Process∞ i A → Process∞ i B  
  fmap∞i {A} {B} f {i}  =  fmap∞ {A} {B} f i 
