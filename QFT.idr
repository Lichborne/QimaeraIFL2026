module QFT

import Data.Nat
import Data.Vect
import Decidable.Equality
import Injection
import QuantumOp
import LinearTypes
import UStateT
import QStateT
import UnitaryLinear
import Lemmas
import UnitarySim
import UnitaryMatrixSim
import SimulatedOp
import QuditMatrix


%default total

|||Quantum circuit for the Quantum Fourier Transform

-------------------------------------------------
-- Old QFT implementation using Unitary
-------------------------------------------------

--CONTROLLED PHASE GATES FOR THE QFT

||| Phase gate with phase 2 pi / (2^m)
RmOld : Nat -> Unitary 1
RmOld m = PGate (2 * pi / (pow 2 (cast m)))

public export
||| Controlled phase gate with phase 2 pi / (2^m)
cRmOld : Nat -> Unitary 2
cRmOld m = controlled (RmOld m)


||| Auxiliary function for QFT : builds the recursive pattern
||| n -- number of qubits
export
qftRecOld : (n : Nat) -> Unitary n
qftRecOld 0 = IdGate
qftRecOld 1 = HGate
qftRecOld (S (S k)) = case decInj (S (k + 1)) [(S k ), 0] of -- this will always be trivially true, but we get the proof for free this way
    Yes prfYes =>
        let t1 = (qftRecOld (S k)) # IdGate
        in rewrite sym $ lemmaplusOneRight k in apply (cRmOld (S (S k))) t1 [(S k ), 0] {prf = prfYes}
    No _ => IdGate 


||| QFT unitary circuit for n qubits
|||
||| n -- number of qubits
export
qftOld : (n : Nat) -> Unitary n
qftOld 0 = IdGate
qftOld (S k) = 
  let g = qftRecOld (S k)
      h = (IdGate {n = 1}) # (qftOld k)
  in h . g

-------------------------------------------------
-- New QFT implementations using UnitaryOp 
-- (fully monadic and semi-monadic)
-------------------------------------------------

||| Builds the UnitaryOp with one's own version of a unitary; with the target being the first 
||| qubit in LVect (so if only one is passed, it is obviously that, which is how this is usually
||| expected to be used)
Rm : UnitaryOp t => {n:Nat} -> Nat -> (1_: LVect 1 Qubit) -> UStateT (t n) (t n) (LVect 1 Qubit)
Rm m [q] = do
  [q] <- applyP (2 * pi / (pow 2 (cast m))) q
  pure [q]

export
||| Builds the UnitaryOp (abstract) version of cRmOld
cRm : UnitaryOp t => {n:Nat} -> Nat -> (1_: Qubit) -> (1_: Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)
cRm {n} m c u = multipleControlUST [c] [u] ((Rm m))

||| alternative using concrete control and buildunitary
cRmAlt : UnitaryOp t => {n:Nat} -> Nat -> (1_: Qubit) -> 
        (1_: Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)
cRmAlt {n = Z} m c u = pure [c, u] -- this is if t n is empty, which cannot be the case if we have two qubits
cRmAlt {n = S k} m c u = do 
                cu <- applyControlledOwn {i = 1} c [u] (buildUnitary (Rm m))
                pure cu

||| Builds the *abstract* rotation operator for the QFT inside UnitaryOp
rotate : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (S i) Qubit)
rotate m q [] = pure (q :: [])
rotate m q (p::ps) = do
        [p', q'] <- cRm m p q 
        (q'' :: ps') <- rotate (S m) q' ps 
        pure (q'':: p':: ps')

||| Builds the *abstract* operator for the QFT inside UnitaryOp using rotation
public export
qft :  UnitaryOp t => {n:Nat} -> {i:Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (i) Qubit)
qft [] = pure []
qft {n = Z} (q::qs) = pure (q::qs)
qft (q::qs) = do
    [q']<- applyH q
    (q'' :: qs') <- rotate (2) q' qs 
    qs'' <- qft qs'
    pure (q'' :: qs'')

||| Full, fully abstract QFT
public export
qftQ : UnitaryOp t => QuantumOp t => (n: Nat) -> {i:Nat} -> (1 _ : LVect i Qubit) -> QStateT (t n) (t n) (LVect i Qubit)
qftQ n {i} qs = applyUST {t=t} (qft {t=t} {i = i} {n = n} (qs))

--------------------------------
|||| Original QFT-like UnitaryOp
--------------------------------

qftRec : UnitaryOp t => {n:Nat} -> {i:Nat} -> (1 _ : LVect i Qubit) -> 
                            UStateT (t (n)) (t (n)) (LVect (i) Qubit)
qftRec {i = Z} [] = pure []
qftRec {i = S Z} [q] = applyH q
qftRec {i = (S (S k))} (q::qs) = do
   (qs # [c]) <- splitLastUtil (q::qs)
   (t::qs) <- qftRec qs
   [c, t] <- cRm (S (S k)) c t
   qst <- combineSingleR qs t
   pure (c::qst)

||| QFT unitary circuit for n qubits, n -- number of qubits
export
qftOldOp : UnitaryOp t => {n:Nat} -> {i:Nat} -> (1 _ : LVect i Qubit) -> 
                            UStateT (t (n)) (t (n)) (LVect (i) Qubit)
qftOldOp []= pure []
qftOldOp (q::qs)  = do
    (q::rec) <- qftRec (q::qs)
    qs <- (qftOldOp rec)
    pure (q::qs)


---------------------------------------------------
||| Semi-Monadic QFT using Unitary via applyUnitary
---------------------------------------------------

||| Builds the rotation operator for the QFT inside UnitaryOp using the unitaries built with Unitary
rotateU : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (S i) Qubit)
rotateU m q [] = pure (q :: [])
rotateU {n} {i = (S k)} m q (p::ps) = do
        [p', q']<- applyUnitary [p, q] (cRmOld m)
        (q'' :: ps') <- rotateU (S m) q' ps
        pure (q'':: p':: ps')

||| Builds the whole operator for the QFT inside UnitaryOp using rotation using the unitaries built with Unitary
public export
qftU :  UnitaryOp t => {n:Nat} -> {i:Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (i) Qubit)
qftU [] = pure []
qftU {n} {i = S k} (q::qs) = do
    [q'] <- applyUnitary [q] HGate
    (q'' :: qs') <- rotateU (2) q' qs
    qs'' <- qftU qs'
    pure (q'' :: qs'')


||| Full, partially abstract QFT
public export
qftUQ : UnitaryOp t => QuantumOp t => (i : Nat) -> (n: Nat) -> (1 _ : LVect i Qubit) -> QStateT (t n) (t n) (LVect i Qubit)
qftUQ i n qs = applyUST {t=t} (qftU {t=t} {i = i} {n = n} (qs))

---------------- Manual inversion of QFT ------------------
|||Was used for testing
-----------------------------------------------------------
||| Builds the rotation operator for the QFT inside UnitaryOp using the unitaries built with Unitary
rotateAdjManual : UnitaryOp t => {n:Nat} -> {i:Nat} -> (m:Nat) -> (1_ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (S i) Qubit)
rotateAdjManual m q [] = pure (q :: [])
rotateAdjManual {n} {i = (S k)} m q (p::ps) = do
        (q' :: ps') <- rotateAdjManual (S m) q ps
        (p' :: [q'']) <- applyUnitary (p :: [q']) (adjoint (cRmOld m))
        pure (q'':: p':: ps')

||| Builds the whole operator for the QFT inside UnitaryOp using rotation using the unitaries built with Unitary
public export
qftUAdjManual :  UnitaryOp t => {n:Nat} -> {i:Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (i) Qubit)
qftUAdjManual [] = pure []
qftUAdjManual {n} {i = S k} (q::qs) = do
    qs' <- qftUAdjManual qs
    (q' :: qs'') <- rotateAdjManual (S (S Z)) q qs'
    (q'' :: Nil ) <- applyUnitary [q'] (adjoint HGate)
    pure (q'' :: qs'')

-------------------------------------------------------------
||| suggested method for inverting UnitaryOp-built unitaries   
------------------------------------------------------------
public export 
qftAdj : UnitaryOp t => {n:Nat} -> {i:Nat} -> (1 _ : LVect i Qubit) -> UStateT (t (n)) (t (n)) (LVect (i) Qubit)
qftAdj lvect = adjointUST (qft lvect)

||| Full, partially abstract QFT
public export
qftQAdj : UnitaryOp t => QuantumOp t => (i : Nat) -> (n: Nat) -> (1 _ : LVect i Qubit) -> QStateT (t n) (t n) (LVect i Qubit)
qftQAdj i n qs = applyUST {t=t} (qftAdj {t=t} {i = i} {n = n} (qs))

---------------------- TESTS ------------------------

||| Run with 3 qubits with SimulatedOp(any more takes too long on a normal computer)
runQFT3 : UnitaryOp t => QuantumOp t => IO (Vect 3 Bool)
runQFT3 = runQ {t=t} (do
    [q1,q2,q3] <- newQubits 3
    qfts <- applyUST (qft ([q3,q2,q1]))
    measureAll qfts)

||| build qft unitary, based on size n
export
qftInT: UnitaryOp t => {n:Nat} -> t n
qftInT = buildUnitary (qft)

||| build qft unitary, based on size n
export
qftInUnitary : {n:Nat} -> Unitary n
qftInUnitary {n} = qftInT {t = Unitary}

||| build qft unitary, based on size n, with unitary used internally
export
qftUInT : UnitaryOp t => {n:Nat} -> t n
qftUInT = buildUnitary (qftU)

||| build qft unitary, based on size n, with unitary used internally
export
qftUInUnitary : {n:Nat} -> Unitary n
qftUInUnitary {n} = qftUInT {t = Unitary}

||| build unitary matrix
export
qftInUnitaryMatrix : (n:Nat) -> UnitaryMatrix n
qftInUnitaryMatrix n = qftInT {t = UnitaryMatrix} {n = n}

||| shuffle around the qubits (just reverse, in this case)
export
qftUnitaryShuffle : Unitary 3
qftUnitaryShuffle  = runUnitaryOp (do
    [q1,q2,q3] <- supplyQubits 3
    qs <- applyUStateT (qft [q3,q2,q1])
    pure qs)


||| run unitary simple for 3 qubits via quantumop
export    
runQFT3U : QuantumOp t => IO (Vect 3 Bool)
runQFT3U = runQ {t=t} (do
    [q1,q2,q3] <- newQubits 3
    qfts <- applyUnitaryDirectly (qftInUnitary) [q3,q2,q1]
    measureAll qfts)
    


public export
||| Run with 3 qubits with SimulatedOp(any more takes too long on a normal computer)
qftQOp : UnitaryOp t => QuantumOp t => (n:Nat) -> QStateT (t 0) (t 0) (Vect n Bool)
qftQOp n = do
    qs <- newQubits n
    qfts <- applyUST (qft (qs))
    measureAll qfts

public export 
||| Test with 3 qubits with SimulatedOp    
testQFT3 : IO (Vect 3 Bool)
testQFT3 = runQ {t = SimulatedOp} (qftQOp 3)


||| build the qudit matrix based on Unitary for any base.
||| e.g. qftQuditUM 2 3 is the same as qftInUnitaryMatrix 3
export
qftQuditUM : (base:Nat) -> (n:Nat) -> QuditUM base n
qftQuditUM base n = unitaryToQuditUM base (qftInUnitary {n = n})


