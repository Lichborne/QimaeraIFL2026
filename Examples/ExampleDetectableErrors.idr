module Examples.ExampleDetectableErrors

import Data.Nat
import Data.Vect
import Data.List
import Utilities.LinearTypes
import Control.Linear.LIO
import Utilities.UnitaryLinear
import Qimaera.Lib.QStateT
import System.Random
import Utilities.Injection
import Utilities.Complex
import Qimaera.Lib.QuantumOp
import Qimaera.Lib.ConcreteImplementations.SimulatedOp
import Examples.Examples
import Qimaera.Lib.UStateT
import Algorithms.QFT


--%search_timeout 1 

--%auto_implicit_depth 15


-------------------------------------- Impossible Unitaries ---------------------------------------
-- In this example, we try to apply a Hadamard gate on a non-existing wire (index 4 on a gate of size 3)
{-
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

-- Error: While processing right hand side of brokenApply1.When unifying: 
--Unitary 2 Unitary ?i Mismatch between: Unitary 2 and Unitary ?i.


-- In this example, we try to apply a circuit twice on the same wire

brokenApply2 : Unitary 3
brokenApply2 = apply toffoli IdGate [1,2,1]

-- Error: While processing right hand side of brokenApply2. Can't find an implementation for IsInjectiveT 3 [1, 2, 1].

--------------------------------- BROKEN UnitaryOp OPERATIONS ---------------------------------

-- Double reference 
rotateBad : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
rotateBad m q (p::ps) = do
  [p', q'] <- cRm m q q          -- should be: cRm m p q
  (q'' :: ps') <- rotateBad (S m) q' ps
  pure (q'' :: p' :: ps')

--Error: While processing right hand side of rotate. There are 2 uses of linear name q.

-- a controlled pattern trying to use a qubit from outside.
cRmBad : UnitaryOp t => {n:Nat} -> Nat -> (1_: Qubit) -> (1_: Qubit) -> (1_: Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)
cRmBad m c u a = multipleControlUST [c] [u] (\vs => do
                (a' :: vs') <- applyUnitary (a :: vs) (cRmOld m)
                pure vs')
-- Error: ... a is not accessible in this context.

-- A one-qubit gate applied to two qubits. The length index: LVect 2 against Unitary 1.
uBad : UnitaryOp t => {n:Nat} -> (1_ : Qubit) -> (1_ : Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)
uBad q p = applyUnitary [q, p] HGate

-- Error: While processing right hand side of uBad... Mismatch between: 0 and 1.

--------- Other UnitaryOp Errors that help making sure definitions are carefully set up but are the necessity would not exist without the monadic structure -------

--  Continuing with the old handle q instead of the returned q'. q was consumed by cRm.
rotateBad2 : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
rotateBad2 m q [] = pure [q]
rotateBad2 m q (p::ps) = do
    [p', q'] <- cRm m p q
    (q'' :: ps') <- rotateBad2 (S m) q ps
    pure (q'' :: p' :: ps')

--Error: While processing right hand side of rotate. q is not accessible in this context.

-- The length index of LVect: the result has one qubit too few.
rotateBad3 : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
rotateBad3 m q [] = pure [q]
rotateBad3 m q (p::ps) = do
    [p', q'] <- cRm m p q
    (q'' :: ps') <- rotateBad3 (S m) q' ps
    pure (q'' :: ps')

--Error: While processing right hand side of rotate... Mismatch between: k and S k


--------------------------------- BROKEN QuantumOp+UnitaryOp OPERATIONS ---------------------------------


-- In this example, wew try to reuse a qubit that has be measured
ux :  UnitaryOp t => {n: Nat} -> (1 _ : LVect 3 Qubit) -> UStateT (t n) (t n) (LVect 3 Qubit)
ux qs = do 
      qs <- applyUnitary qs {i = 3} toffoli
      pure qs
    

brokenOp1 : UnitaryOp t => QuantumOp t => QStateT (t 0) (t 0) (Vect 4 Bool)
brokenOp1  = do
      [q1,q2,q3,q4] <- newQubits {t = t} 4
      [b3] <- measure [q3]
      [r4,r3,r1] <- applyUST {t = t} (ux [q4,q3,q1])  --trying to reuse q3
      [b1,b4,b2] <- measure [r1,r4,q2]
      pure ([b1,b2,b3,b4])
      
brokenOp1Run : IO (Vect 4 Bool)
brokenOp1Run = run (do
            bs <- brokenOp1 {t = SimulatedOp}
            pure bs)
       
-- Error: While processing right hand side of brokenOp1. q3 is not accessible in this context.


-- In this example we try to copy a qubit

brokenOp2 : IO (Vect 5 Bool)
brokenOp2 = 
  run (do
      [q1,q2,q3,q4,q5] <- newQubits {t = SimulatedOp} 5
      [b3] <- measure [q3]
      [q4,q1,q2] <- applyUST (ux [q4,q1,q4]) 
      [b1,b2,b4,b5] <- measure [q1,q2,q4,q5]
      pure [b1,b2,b3,b5,b5]
      )

-- " There are 2 uses of linear name q4." This is an example which gives the error with the right issue, but because of a lot of things shadowing one another
-- in the interfaces, instead of seeing that q4 is used twice, it appears to be used 0 times. 
-- Error : While processing right hand side of brokenOp2. There are 2 uses of linear name q4. 


-- In this example, we try to reuse a pointer to an old state of a qubit (the state of the qubit has been modified)

brokenOp3 : IO (Vect 4 Bool)
brokenOp3  = 
  run (do
      [q1,q2,q3,q4] <- newQubits {t = SimulatedOp} 4
      [b3] <- measure [q3]
      [r4,r2,r1] <- applyUST (ux [q4,q2,q1]) 
      [b1,b4,b2] <- measure [r1,r4,q2] --trying to reuse the name q2
      pure ([b1,b2,b3,b4])
      )
      
--Error: While processing right hand side of brokenOp2. q2 is not accessible in this context.
  
--In this example, we try to use a 3 qubit gate on 4.

brokenOp4 : IO (Vect 5 Bool)
brokenOp4 = 
  run (do
      [q1,q2,q3,q4,q5] <- newQubits {t = SimulatedOp} 5
      [b3] <- measure [q3]
      [q4,q1,q2,q5] <- applyUST (ux [q4,q1,q2,q5]) 
      [b1,b2,b5] <- measure [q1,q2,q5]
      pure [b1,b2,b3,b5,b5]
      )
  
-- The error message idris gives is that q5 cannot be made
-- equal in type to LVect 0 Qubit, and it tries a few things it could be that fail. The error message is not ideal, but works.

-- In this example we try to map to the same name twice.

brokenOp5 : IO (Vect 5 Bool)
brokenOp5 = 
  run (do
      [q1,q2,q3,q4,q5] <- newQubits {t = SimulatedOp} 5
      [b3] <- measure [q3]
      [q4,q1,q4] <- applyUST (ux [q4,q1,q2]) 
      [b1,b2,b4,b5] <- measure [q1,q2,q4,q5]
      pure [b1,b2,b3,b5,b5]
      )

--Error: While processing right hand side of brokenOp5. There are 2 uses of linear name q4.
 
  -}