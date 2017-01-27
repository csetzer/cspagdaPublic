module simulator where


open import Size
open import Data.Bool
open import Data.Maybe
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import ooAgda.SizedIO.Base  renaming (force to forceIO; delay to delayIO)
open import ooAgda.SizedIO.Console hiding (main)
open import ooAgda.NativeIO 
open import choiceSetU
open import process 
open Process∞
open Process+
open import showFunction
open import choiceAuxFunction
open import Data.Sum


mutual
   myProgram : ∀ {i} → (c₀ : Choice) 
               → Process ∞  c₀  
               → IOConsole i Unit  
   forceIO (myProgram {i} c₀ P) = do' (putStrLn (Str P)) λ _ → 
                                  myProgram₀ c₀ P (processChoiceIsEmpty P) (processHasSuccessfullyTerminated P)

   myProgram₀ : ∀ {i} → (c₀ : Choice) 
               → Process ∞  c₀ → Bool → Bool  
               → IOConsole i Unit  
   myProgram₀ c₀ P false b =    do (putStrLn ("Termination Events:" ++s showTicks P)) λ _ → 
                                do (putStrLn ("Events" ++s showLabels₁ P))  λ _ → 
                                do (putStrLn ("Choose Event"))  λ _ → 
                                myProgram₁ c₀ P 
   myProgram₀ c₀ P true false = do (putStrLn "Program got stuck") λ _ → 
                                return unit 
   myProgram₀ c₀ P true true =  do (putStrLn "Program has successfully terminated") λ _ → 
                                return unit 

   myProgram₁ : ∀ {i} → (c₀ : Choice) → Process ∞ c₀ 
                      → IOConsole i Unit 
   forceIO (myProgram₁ c₀ P) = do' getLine λ s → myProgram₂ c₀ P s (s ==strb "quit")


   myProgram₂ : ∀ {i} → (c₀ : Choice) → (P : Process ∞ c₀)
                 → String → Bool  
                 → IOConsole i Unit  
   myProgram₂ c₀ P s true  = do (putStrLn "exiting") λ _ → return unit 
   myProgram₂ c₀ P s false = myProgram₃ c₀ P (lookupChoice (processToE P) (processToI P) s)


   myProgram₃ : ∀ {i} → (c₀ : Choice) 
                 → (P : Process ∞ c₀) 
                 → Maybe ((ChoiceSet (processToE P)) ⊎ (ChoiceSet (processToI P)))
                 → IOConsole i Unit  
   forceIO (myProgram₃ c₀ P nothing) = do' (putStrLn "please enter a choice amongst") λ _ →  
                                       do (putStrLn (showLabels₁ P)) λ _ → 
                                       myProgram₁ c₀ P
   myProgram₃ c₀ P (just c₁)         = myProgram c₀ (forcep (processToExternalSubprocess0 P c₁) {∞})


myProgrami : ∀ {i} → {c₀ : Choice} → Process ∞  c₀   → IOConsole i Unit  
myProgrami {i} {c₀} P = myProgram {i} c₀ P
