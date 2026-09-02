module RUS

import Data.Vect
import QStateT
import QuantumOp
import LinearTypes
import UnitaryLinear
import Data.List
import UStateT
import BinarySimulatedOp

||| Problem: Given an input qubit |q> and a single-qubit unitary operation U,
|||          return the state U|q>. The "Repeat Until Success" approach solves
|||          this problem in the following way:
|||
||| 1. Prepare a new qubit in state |0>
||| 2. Apply some two-qubit unitary operation U' (depends on U)
||| 3. Measure the auxiliary qubit
||| 4. With (high) probability the result is now U|q> and then stop.
||| 5. With (low) probability the result is state E|q>, where E is some other unitary operator
|||    (depending on U), so we uncompute the error by applying E^dagger and we go back to step 1.
||| For more information, see https://arxiv.org/abs/1311.1074

export
RUS : UnitaryOp t => QuantumOp t => (1 _ : Qubit) -> (u' : Unitary 2) -> (e : Unitary 1) -> QStateT (t 1) (t 1) Qubit
RUS q u' e = do
  q' <- newQubit
  [q',q] <- applyUST (applyUnitary [q',q] u')
  b <- measureQubit q'
  if b then do
         [q] <- applyUST (applyUnitary [q] (adjoint e))
         RUS q u' e
       else pure q 

RUSNew : UnitaryOp t => QuantumOp t => (u' : Unitary 2) -> (e : Unitary 1) -> (1 _ : Qubit) -> QStateT (t 1) (t 1) Qubit
RUSNew u' e q = RUS q u' e

||| Figure 8 of https://arxiv.org/abs/1311.1074
export
example_u' : Unitary 2
example_u' = H 0 $ T 0 $ CNOT 0 1 $ H 0 $ CNOT 0 1 $ T 0 $ H 0 IdGate

export
runRUS : UnitaryOp t => QuantumOp t => IO Bool
runRUS = do
  [b] <- runQ (do
              q <- newQubit {t = t}
              q <- RUS q example_u' TGate
              measure [q]
         )
  pure b

export
testRUS : IO Bool
testRUS = runRUS {t = BinarySimulatedOp}

export
RUS_U2 : UnitaryOp t => (1_: LVect 2 Qubit) -> (Unitary 2) -> (UStateT (t 2) (t 2) (LVect 2 Qubit))
RUS_U2 q u' = do
  [q2, q2']<- applyUnitary q u'
  pure [q2, q2']

RUS_U1 : UnitaryOp t => (1_: LVect 1 Qubit) -> (Unitary 1) -> (UStateT (t 1) (t 1) (LVect 1 Qubit))
RUS_U1 q u' = do
  q' <- applyUnitary q u'
  pure q'

RUSAbs : QuantumOp t => UnitaryOp t => (1 _ : Qubit) -> (u' : (1_: LVect 2 Qubit) -> (UStateT (t 2) (t 2) (LVect 2 Qubit))) 
      -> (e : (1_: LVect 1 Qubit) -> (UStateT (t 1) (t 1) (LVect 1 Qubit))) -> QStateT (t 1) (t 1) (LVect 1 Qubit)
RUSAbs q u' e = do
    q' <- newQubit
    [q',q] <- applyUST (u' [q',q])
    b <- measureQubit q'
    if b then do
            [r] <- (applyUST (e [q]))
            RUSAbs r u' e
          else pure [q]

--example_u1 : QuantumOp t => UnitaryOp t => t 2

example_uAbs : UnitaryOp t => (1_: LVect 2 Qubit) -> (UStateT (t 2) (t 2) (LVect 2 Qubit))
example_uAbs [q0, q1] = do
  [q0] <- applyH q0
  [q0] <- applyP (0.7854) q0
  [q0, q1] <- applyCNOT q0 q1 
  [q0] <- applyH q0
  [q0, q1] <- applyCNOT q0 q1 
  [q0] <- applyP (0.7854) q0
  pure [q0, q1]

idAbs : UnitaryOp t => (1_: LVect 1 Qubit) -> (UStateT (t 1) (t 1) (LVect 1 Qubit))
idAbs q = pure q
{-
||| Figure 8 of https://arxiv.org/abs/1311.1074
example_u' : Unitary n
example_u' = H 0 $ T 0 $ CNOT 0 1 $ H 0 $ CNOT 0 1 $ T 0 $ H 0 IdGate
-}
export
runRUSAbs : QuantumOp t => UnitaryOp t => IO Bool
runRUSAbs = do
  [b] <- runQ (do
              q <- newQubit {t = t}
              q <- RUSAbs q (example_uAbs) idAbs
              measure q
         )
  pure b

export
testRUSAbs : IO Bool
testRUSAbs = runRUS {t = BinarySimulatedOp}

export
testMultipleRUS : Nat -> IO ()
testMultipleRUS n = do
  let f = testRUS
  s <- sequence (Data.List.replicate n f)
  let heads = filter (== True) s
  putStrLn $ "Number of '1' outcomes: " ++ (show (length heads)) ++ " out of " ++ (show n) ++ " measurements."
{--}