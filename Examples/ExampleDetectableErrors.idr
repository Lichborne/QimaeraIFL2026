||| Programs that Idris must reject. Each example sits in a `failing` block, which compiles only if
||| its contents fail to typecheck with an error containing the given message, so checking this
||| module checks every example, including the errors quoted in the paper:
|||   idris2 -p contrib -p linear --check Examples/ExampleDetectableErrors.idr
||| The last section checks what client code (any module outside Qimaera.Lib) cannot do.
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

-- In this example, we try to apply a Hadamard gate on a non-existing wire (index 5 on a gate of size 3)
failing "Can't find an implementation for LTE 6 3"
  brokenH : Unitary 3
  brokenH = H 5 toffoli

-- In this example, we try to apply the control and the target of a CNOT on the same wire
failing "Can't find an implementation for Either (LTE 2 1) (LTE 2 1)"
  brokenCNOT : Unitary 2
  brokenCNOT = CNOT 1 1 IdGate

-- In this example, we try to apply a circuit on a non existing wire (index 4 on a gate of size 3)
failing "Can't find an implementation for IsInjectiveT 3 [1, 4]"
  brokenApply1 : Unitary 3
  brokenApply1 = apply toBellBasis toffoli [1,4]

-- In this example, we try to apply a circuit twice on the same wire
failing "Can't find an implementation for IsInjectiveT 3 [1, 2, 1]"
  brokenApply2 : Unitary 3
  brokenApply2 = apply toffoli IdGate [1,2,1]

--------------------------------- BROKEN UnitaryOp OPERATIONS ---------------------------------

-- Double reference
failing "There are 2 uses of linear name q."
  rotateBad : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
  rotateBad m q (p::ps) = do
    [p', q'] <- cRm m q q          -- should be: cRm m p q
    (q'' :: ps') <- rotateBad (S m) q' ps
    pure (q'' :: p' :: ps')

-- a controlled pattern trying to use a qubit from outside.
failing "a is not accessible in this context."
  cRmBad : UnitaryOp t => {n:Nat} -> Nat -> (1_: Qubit) -> (1_: Qubit) -> (1_: Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)
  cRmBad m c u a = multipleControlUST [c] [u] (\vs => do
                  (a' :: vs') <- applyUnitary (a :: vs) (cRmOld m)
                  pure vs')

-- A one-qubit gate applied to two qubits. The length index: LVect 2 against Unitary 1.
failing "Mismatch between: 0 and 1."
  uBad : UnitaryOp t => {n:Nat} -> (1_ : Qubit) -> (1_ : Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)
  uBad q p = applyUnitary [q, p] HGate

--------- Other UnitaryOp Errors that help making sure definitions are carefully set up but are the necessity would not exist without the monadic structure -------

--  Continuing with the old handle q instead of the returned q'. q was consumed by cRm.
failing "q is not accessible in this context."
  rotateBad2 : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
  rotateBad2 m q [] = pure [q]
  rotateBad2 m q (p::ps) = do
      [p', q'] <- cRm m p q
      (q'' :: ps') <- rotateBad2 (S m) q ps
      pure (q'' :: p' :: ps')

-- The length index of LVect: the result has one qubit too few.
failing "Mismatch between: k"
  rotateBad3 : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
  rotateBad3 m q [] = pure [q]
  rotateBad3 m q (p::ps) = do
      [p', q'] <- cRm m p q
      (q'' :: ps') <- rotateBad3 (S m) q' ps
      pure (q'' :: ps')


--------------------------------- BROKEN QuantumOp+UnitaryOp OPERATIONS ---------------------------------

-- A valid three-qubit unitary, used by the examples below.
ux :  UnitaryOp t => {n: Nat} -> (1 _ : LVect 3 Qubit) -> UStateT (t n) (t n) (LVect 3 Qubit)
ux qs = do
      qs <- applyUnitary qs {i = 3} toffoli
      pure qs

-- In this example, we try to reuse a qubit that has been measured
failing "q3 is not accessible in this context."
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

-- In this example we try to copy a qubit
failing "There are 2 uses of linear name q4."
  brokenOp2 : IO (Vect 5 Bool)
  brokenOp2 =
    run (do
        [q1,q2,q3,q4,q5] <- newQubits {t = SimulatedOp} 5
        [b3] <- measure [q3]
        [q4,q1,q2] <- applyUST (ux [q4,q1,q4])
        [b1,b2,b4,b5] <- measure [q1,q2,q4,q5]
        pure [b1,b2,b3,b5,b5]
        )

-- In this example, we try to reuse a pointer to an old state of a qubit (the state of the qubit has been modified)
failing "q2 is not accessible in this context."
  brokenOp3 : IO (Vect 4 Bool)
  brokenOp3  =
    run (do
        [q1,q2,q3,q4] <- newQubits {t = SimulatedOp} 4
        [b3] <- measure [q3]
        [r4,r2,r1] <- applyUST (ux [q4,q2,q1])
        [b1,b4,b2] <- measure [r1,r4,q2] --trying to reuse the name q2
        pure ([b1,b2,b3,b4])
        )

-- In this example, we try to use a 3 qubit gate on 4.
-- The error message is not ideal (Idris tries to make q5 equal in type to LVect 0 Qubit), but works.
failing
  brokenOp4 : IO (Vect 5 Bool)
  brokenOp4 =
    run (do
        [q1,q2,q3,q4,q5] <- newQubits {t = SimulatedOp} 5
        [b3] <- measure [q3]
        [q4,q1,q2,q5] <- applyUST (ux [q4,q1,q2,q5])
        [b1,b2,b5] <- measure [q1,q2,q5]
        pure [b1,b2,b3,b5,b5]
        )

-- In this example we try to map to the same name twice.
failing "There are 2 uses of linear name q4."
  brokenOp5 : IO (Vect 5 Bool)
  brokenOp5 =
    run (do
        [q1,q2,q3,q4,q5] <- newQubits {t = SimulatedOp} 5
        [b3] <- measure [q3]
        [q4,q1,q4] <- applyUST (ux [q4,q1,q2])
        [b1,b2,b4,b5] <- measure [q1,q2,q4,q5]
        pure [b1,b2,b3,b5,b5]
        )

--------------------------------- RESTRICTIONS ON CLIENT CODE ---------------------------------
-- This module is client code: it is outside the Qimaera.Lib namespace.

-- Forging a qubit handle
failing "MkQubit is private."
  forgedQubit : Qubit
  forgedQubit = MkQubit 0

-- Opening a simulator state to get at the handles it holds
failing "MkSimulatedOp is private."
  handlesOf : SimulatedOp n -> Vect n Qubit
  handlesOf (MkSimulatedOp _ _ v _) = v

-- Writing a unitary step by hand instead of through UnitaryOp
failing "MkUST is private."
  fakeStep : UStateT (SimulatedOp n) (SimulatedOp n) ()
  fakeStep = MkUST (\s => s # ())

-- Running a unitary computation on a state outside the interfaces
failing "runUStateT is private."
  runOutside : (1 _ : SimulatedOp n) -> (1 _ : UStateT (SimulatedOp n) (SimulatedOp n) a) -> LPair (SimulatedOp n) a
  runOutside s act = runUStateT s act

-- Writing a quantum step by hand instead of through QuantumOp
failing "MkQST is private."
  fakeQuantumStep : QStateT (SimulatedOp n) (SimulatedOp n) ()
  fakeQuantumStep = MkQST (\s => pure1 (s # ()))

-- Running a quantum computation on a state outside the interfaces
failing "runQStateT is private."
  runQuantumOutside : (1 _ : SimulatedOp n) -> (1 _ : QStateT (SimulatedOp n) (SimulatedOp n) a) -> L IO {use = 1} (LPair (SimulatedOp n) a)
  runQuantumOutside s act = runQStateT s act

-- Replacing the state of a computation
failing "modify"
  replaceState : UStateT (SimulatedOp n) (SimulatedOp n) ()
  replaceState = modify (\s => s)
