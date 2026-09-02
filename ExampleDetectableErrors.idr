module ExampleDetectableErrors

import Data.Nat
import Data.Vect
import Data.List
import LinearTypes
import Control.Linear.LIO
import UnitaryLinear
import QStateT
import System.Random
import Injection
import Complex
import QuantumOp
import SimulatedOp
import Examples
import UStateT


--%search_timeout 1 

--%auto_implicit_depth 15


-------------------------------------- Impossible Unitaries ---------------------------------------
-- In this example, we try to apply a Hadamard gate on a non-existing wire (index 4 on a gate of size 3)
{-}
brokenH : Unitary 3
brokenH = H 5 toffoli

-- Error: While processing right hand side of brokenH. Can't find an implementation for LT 5 3.




-- In this example, we try to apply the control and the target of a CNOT on the same wire

brokenCNOT : Unitary 2
brokenCNOT = CNOT 1 1 IdGate

-- Error: While processing right hand side of brokenCNOT. Can't find an implementation for Either (LTE 2 1) (LTE 2 1).


-- In this example, we try to apply a circuit on a non existing wire (index 4 on a gate of size 3)

brokenApply1 : Unitary 3
brokenApply1 = apply toBellBasis toffoli [1,4]

-- Error: While processing right hand side of brokenApply1.When unifying: Unitary 2 Unitary ?i Mismatch between: Unitary 2 and Unitary ?i.




-- In this example, we try to apply a circuit twice on the same wire

brokenApply2 : Unitary 3
brokenApply2 = apply toffoli IdGate [1,2,1]

-- Error: While processing right hand side of brokenApply2. Can't find an implementation for IsInjectiveT 3 [1, 2, 1].

--------------------------------- BROKEN QUANTUM STATE OPERATIONS ---------------------------------

-- In this example, wew try to reuse a qubit that has be measured
ux :  UnitaryOp t => {n: Nat} -> (1 _ : LVect 3 Qubit) -> UStateT (t n) (t n) (LVect 3 Qubit)
ux qs = do 
      qs <- applyUnitary qs {i = 3} toffoli
      pure qs
    

brokenOp1 : UnitaryOp t => QuantumOp t => QStateT (t 0) (t 0) (Vect 4 Bool)
brokenOp1  = do
      [q1,q2,q3,q4] <- newQubits {t = t} 4
      [b3] <- measure [q3]
      [r4,r3,r1] <- applyUST {t = t} (applyUnitaryAbs (ux [q4,q3,q1]))  --trying to reuse q3
      [b1,b4,b2] <- measure [r1,r4,q2]
      pure ([b1,b2,b3,b4])
      
brokenOp1Run : IO (Vect 4 Bool)
brokenOp1Run = runQ (do
            bs <- brokenOp1 {t = SimulatedOp}
            pure bs)
       
-- Error: While processing right hand side of brokenOp1. q3 is not accessible in this context.



-- In this example, we try to copy a qubit

brokenOp2 : IO (Vect 5 Bool)
brokenOp2 = 
  runQ (do
      [q1,q2,q3,q4] <- newQubits {t = SimulatedOp} 4
      [b3] <- measure [q3]
      [q4,q1,q5] <- applyUST (applyUnitary [q4,q1,q4] (X 0 IdGate)) --trying to copy q4
      [b1,b2,b5] <- measure [q1,q2,q5]
      pure [b1,b2,b3,b5,b5]
      )
      
--This is an example which gives the error with the right issue, but because of a lot of things shadowing one another
-- in the interfaces, instead of seeing that q4 is used twice, it appears to be used 0 times. 
-- Error : While processing right hand side of brokenOp2. There are 0 uses of linear name q4. 



-- In this example, we try to reuse a pointer to an old state of a qubit (the state of the qubit has been modified)

brokenOp3 : IO (Vect 4 Bool)
brokenOp3  = 
  runQ (do
      [q1,q2,q3,q4] <- newQubits {t = SimulatedOp} 4
      [b3] <- measure [q3]
      [r4,r2,r1] <- applyUST (applyUnitary [q4,q2,q1] (X 0 IdGate)) 
      [b1,b4,b2] <- measure [r1,r4,q2] --trying to reuse the name q2
      pure ([b1,b2,b3,b4])
      )
      
--Error: While processing right hand side of brokenOp2. q2 is not accessible in this context.
  -}
  