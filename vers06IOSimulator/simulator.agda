module simulator where


open import Size
open import Data.Bool
open import Data.Maybe
open import Data.String renaming  (_==_ to _==strb_; _++_ to _++s_)
open import SizedIO.Base  renaming (force to forceIO; delay to delayIO)
open import SizedIO.Console hiding (main)
open import NativeIO
open import choiceSetU
open import process 
open ∞Process
open import showFunction
open import choiceAuxFunction
open import Data.Sum


mutual
   myProgram : ∀ {i} → (c0 : Choice) → Process ∞  (ChoiceSet c0)  → IOConsole i Unit  
   forceIO (myProgram {i} c0 P) = do' (putStrLn (showProcess c0 P))    λ _ → 
                                  myProgram0 c0 P (processChoiceIsEmpty P) (processHasSuccessfullyTerminated P)

   myProgram0 : ∀ {i} → (c0 : Choice) → Process ∞  (ChoiceSet c0)  → Bool → Bool → IOConsole i Unit  
   myProgram0 c0 P false b = do (putStrLn (showLabels₁ P))  λ _ → 
                             do (putStrLn ("Enter a choice"))  λ _ → 
                              myProgram1 c0 P 
   myProgram0 c0 P true false = do (putStrLn "Program got stuck") λ _ → 
                               return unit
   myProgram0 c0 P true true = do (putStrLn "Program has successfully terminated") λ _ → 
                               return unit
--                                   do (putStrLn (showLabels₁ P))  λ _ → 
--                                   do (putStrLn ("Enter a choice"))  λ _ → 
--                                   myProgram1 c0 P 
-- choiceIsEmpty

   myProgram1 : ∀ {i} → (c0 : Choice) → Process ∞ (ChoiceSet c0) → IOConsole i Unit 
   forceIO (myProgram1 c0 P) = do' getLine λ s → myProgram2a c0 P s (s ==strb "quit")


   myProgram2a : ∀ {i} → (c0 : Choice) → (P : Process ∞ (ChoiceSet c0)) → String → Bool  → IOConsole i Unit  
   myProgram2a c0 P s true = do (putStrLn "exiting") λ _ → return unit
   myProgram2a c0 P s false = myProgram2 c0 P (lookupChoice (processToE P) (processToI P) s)


   myProgram2 :  ∀ {i} → (c0 : Choice) 
                 →  (P : Process ∞ (ChoiceSet c0)) 
                 →  Maybe (  (ChoiceSet (processToE P)) ⊎ (ChoiceSet (processToI P) ))
                 →  IOConsole i Unit  
   forceIO (myProgram2 c0 P nothing) = do' (putStrLn "please enter a choice amongst") λ _ →  
                                    do (putStrLn (showLabels₁ P)) λ _ → 
                                    myProgram1 c0 P
   myProgram2 c0 P (just c1) =  myProgram c0 (force (processToExternalSubprocess0 P c1) ∞ )


