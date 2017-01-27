module codeAsInTyDe2016Paper where


-- This file loads the files as they occur
-- in the TyDe2016 paper by Bashar Igried and Anton Setzer


--- Sect. 1  Introduction

--- Sect. 2  CSP

--  Sect. 3 Agda

open import finn
open import exampleFinFun
open import eliminationExample

-- Sect. 4 The library CSP-Agda

-- Sect. 4.1. Representing CSP Processes in Agda

open import process
open import choiceSetU

-- Sect. 4.2. Sequential Composition}

open import sequentialComposition

-- Sect. 4.3 Recursion

open import rec

-- Sect. 4.4. STOP, SKIP, terminate, DIV}%, and Prefix

open import efq
open import primitiveProcess
open import skip
open import div

-- Sect. 4.5. Prefix 

open import preFix

-- Sect. 4.6. Internal Choice

open import internalChoice


-- Sect. 4.7. External Choice

open import externalChoice
open import addTick
open import renamingResult

-- Sect. 4.8. Renaming

open import renamingOperator

-- Sect. 4.9 Parallel Operator, Interleaving, and Interrupt

open import interleave

-- Not included in paper: Interrupt
open import parallelSimple
open import interrupt

-- Sect. 4.10. Hiding

open import hidingOperator

-- Sect. 5. A Simulator of CSP-Agda

open import simulatorCutDown

-- Full version of simulator not in paper

open import simulator

-- Sect. 6. Related Work

-- Sect. 7. Conclusion

