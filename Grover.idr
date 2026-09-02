module Grover

import Data.Nat
import Data.Vect
import Decidable.Equality
import UnitaryLinear
import Injection
import LinearTypes
import Lemmas
import Control.Linear.LIO
import QStateT
import AlterningBitsOracle
import QuantumOp
import UStateT
--import UnitaryOp


%default total

|||GROVER'S ALGORITHM
|||1. Start with |0> ¤ n
|||2. Apply H ¤ n
|||3. Grover iteration
|||   3.1 : Apply oracle
|||   3.2 : Apply H ¤ n
|||   3.3 : Amplification
|||   3.4 : Apply H ¤ n


------------- AMPLIFICATION-------------

public export total
amplification : (n : Nat) -> Unitary n
amplification 0 = IdGate
amplification 1 = IdGate
amplification (S k) = 
  let x = tensorn (S k) (X 0 IdGate)
      h1 = H k x
      c = generalizedToffoli (S k) . h1
      h2 = H k c
  in x . h2 

---------------ANCILLAE----------------------

xhAncilla : (p : Nat) -> Unitary p
xhAncilla 0 = IdGate
xhAncilla (S p) = let xh = (H 0 IdGate) . (X 0 IdGate) in rewrite sym $ lemmaplusOneRight p in IdGate # xh

hxAncilla : (p : Nat) -> Unitary p
hxAncilla 0 = IdGate 
hxAncilla (S p) = let xh = (X 0 IdGate) . (H 0 IdGate) in rewrite sym $ lemmaplusOneRight p in IdGate # xh

----------------OG---------------------------

public export total
groverIteration : (n : Nat) -> {p : Nat} -> (oracle : Unitary (n + p)) -> Unitary (n + p)
groverIteration n oracle = 
  let h = tensorn n (H 0 IdGate) 
  in (h # IdGate) . (amplification n # IdGate) . (h # IdGate) . oracle


public export total
repeatGroverIteration : (k : Nat) -> (n : Nat) -> {p : Nat} -> (oracle : Unitary (n + p)) -> Unitary (n + p)
repeatGroverIteration 0 n _ = IdGate
repeatGroverIteration (S k) n oracle = (groverIteration n oracle) . (repeatGroverIteration k n oracle)

public export total
grover' : (n : Nat) -> {p : Nat} -> (oracle : Unitary (n + p)) -> (nbIter : Nat) -> Unitary (n + p)
grover' n oracle nbIter = 
  let h = (tensorn n (H 0 IdGate)) # xhAncilla p
  in (IdGate # hxAncilla p) . (repeatGroverIteration nbIter n oracle) . h

---------------------QUANTUMOP----------------------
public export total
groverIterationOp : UnitaryOp t => (n : Nat) -> {p : Nat} -> (oracle : Unitary (n + p))  -> (1 _ : LVect (n+p) Qubit)-> UStateT (t (n+p)) (t (n+p)) (LVect (n+p) Qubit)
groverIterationOp n oracle qs= 
  let h = tensorn n (H 0 IdGate) 
  in do
    oracled <- applyUnitary (qs) (oracle) -- {n = n+p} {i = n+p} 
    tensored <- applyUnitary (oracled) (tensor h IdGate) --{n = n+p} {i = n+p} 
    amplified <- applyUnitary (tensored) (tensor (amplification n) IdGate) --{n = n+p} {i = n+p} 
    fin <- applyUnitary (amplified) (tensor h IdGate) --{n = n+p} {i = n+p} 
    pure fin

public export total
repeatGroverIterationOp : UnitaryOp t => (k : Nat) -> (n : Nat) -> {p : Nat} -> (oracle : Unitary (n + p)) -> (1 _ : LVect (n+p) Qubit)-> UStateT (t (n+p)) (t (n+p)) (LVect (n+p) Qubit)
repeatGroverIterationOp 0 n _ q = pure q
repeatGroverIterationOp (S k) n oracle (qs) = do 
  rec <- repeatGroverIterationOp k n oracle qs
  fin <- groverIterationOp n oracle rec
  pure fin

public export total
groverOp' : UnitaryOp t => (n : Nat) -> {p : Nat} -> (oracle : Unitary (n + p)) -> (nbIter : Nat) -> (1 _ : LVect (n+p) Qubit)-> UStateT (t (n+p)) (t (n+p)) (LVect (n+p) Qubit)
groverOp' n oracle nbIter qs = 
  let h = tensor (tensorn n (H 0 IdGate)) (xhAncilla p)
  in do
    first <- applyUnitary (qs) (h) -- {n = n+p} {i = n+p}
    grvr <- repeatGroverIterationOp nbIter n oracle first
    fin <- applyUnitary (grvr) (tensor IdGate (hxAncilla p)) -- {n = n+p} {i = n+p}
    pure fin

groverOP : UnitaryOp t => QuantumOp t => (n : Nat) -> {p : Nat} -> (oracle : Unitary (n + p)) -> (nbIter : Nat) -> IO (Vect n Bool)
groverOP n oracle nbIter = do
      w <- runQ (do
            q <- newQubits {t=t} (n + p)
            grvrU <- applyUST (groverOp' {t=t} n oracle nbIter q)
            v <- measureAll grvrU
            pure v
            )
      pure (take n w)



    {-



--------------------------SMALL TEST---------------------------

--Example with the alternating bits oracle

public export
testGrover : IO (Vect 4 Bool)
testGrover = 
  grover {t = SimulatedOp} 4 {p = 1} (solve 2) 1

public export
testG : (nbIter : Nat) -> IO (Vect 3 Nat)
testG 0 = pure [0,0,0]
testG (S k) = do
  [a,b,c] <- testG k
  v <- testGrover
  case v of
       [True,False,True,False] => pure [S a,b,c]
       [False,True,False,True] => pure [a,S b,c]
       _ => pure [a,b,S c]

    -} 

