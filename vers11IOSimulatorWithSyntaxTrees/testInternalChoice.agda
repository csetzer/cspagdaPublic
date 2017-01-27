module testInternalChoice where 


open import process 
open Process∞
open import Size
open import NativeIO
open import showFunction 
open import IOInternalchoice

s : String
s = showLabels₁ (forcep transition₆ {∞})
