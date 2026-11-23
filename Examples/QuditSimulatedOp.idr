||| Proof of concept: a qudit simulator implementing UnitaryOp and QuantumOp. The handles keep
||| their type, Qubit, but each one stands for a qudit of dimension d, and the whole computation is
||| done on qudits.
|||
||| For d = 2 it behaves as SimulatedOp does.
|||
||| Use: Most of the simulator is block 3 below, commented out, because it needs two
||| definitions that can only live elsewhere (blocks 1 and 2):
|||   1. Append block 1 to the end of Qimaera/Lib.idr. 
|||   2. Append block 2 to the end of Qimaera/Lib/QuantumOp.idr. 
|||   3. Uncomment block 3. Qimaera/Lib/: it uses mkUST
|||   4. Move this file to Qimaera/Lib/ConcreteImplementations/QuditSimulatedOp.idr. 
|||   
||| Then import this module and run programs with t = QuditSimulatedOp d, for example
||| run {t = QuditSimulatedOp 3} ..., or load this file in the REPL and enter :exec quditDemo.
|||
||| The algorithms in Algorithms/ run on qudits, but they are written for qubits and do not
||| become their qudit counterparts: qft on qutrits, for instance, is not the qutrit Fourier
||| transform, because its controlled rotations are the qubit ones.

--module Qimaera.Lib.ConcreteImplementations.QuditSimulatedOp
module Qimaera.Examples.QuditSimulatedOp

import Data.Vect
import Data.Nat
import Data.Fin
import Data.List
import System.Random
import Control.Linear.LIO
import Utilities.LinearTypes
import Utilities.UnitaryLinear
import Utilities.Complex
import Utilities.Matrix
import Utilities.QuditMatrix
import Utilities.Lemmas
import Qimaera.Lib
import Qimaera.Lib.UStateT
import Qimaera.Lib.QStateT
import Qimaera.Lib.QuantumOp
import Qimaera.Lib.ConcreteImplementations.QuditMatrixSim

%default total

--------------------------------------------------------------------------------------------------
-- Measuring a qudit
--------------------------------------------------------------------------------------------------

||| The basis states of m qudits are numbered 0 .. d^m - 1, wire 0 being the most significant
||| digit, as everywhere in Qimaera. The digit of basis state r on wire w:
digitOn : (d : Nat) -> (m : Nat) -> (w : Nat) -> (r : Nat) -> Nat
digitOn d m w r = integerToNat ((natToInteger r `div` natToInteger (power d (minus m (S w)))) `mod` natToInteger d)

||| The amplitudes, numbered by basis state.
numbered : Vect l (Vect 1 (Complex Double)) -> List (Nat, Complex Double)
numbered = go 0
  where
    go : Nat -> Vect k (Vect 1 (Complex Double)) -> List (Nat, Complex Double)
    go _ [] = []
    go r ([a] :: rest) = (r, a) :: go (S r) rest

||| The probabilities of the outcomes 0 .. d-1 when the qudit on wire w (of m) is measured.
export
outcomeProbabilities : (d : Nat) -> (m : Nat) -> (w : Nat) -> Vect l (Vect 1 (Complex Double)) -> List Double
outcomeProbabilities d m w amps = map probability (upTo d)
  where
    upTo : Nat -> List Nat
    upTo Z = []
    upTo (S k) = upTo k ++ [k]

    probability : Nat -> Double
    probability k = sum (map (\(r, a) => if digitOn d m w r == k then magnitude a * magnitude a else 0) (numbered amps))

||| The outcome that a random number r in [0, 1) picks, given the outcome probabilities. If
||| rounding leaves r above their total, the last possible outcome is taken.
export
pickOutcome : List Double -> Double -> Nat
pickOutcome ps r = go 0 0 ps
  where
    lastPossible : Nat -> Nat -> List Double -> Nat
    lastPossible best _ [] = best
    lastPossible best k (p :: rest) = lastPossible (if p > 0 then k else best) (S k) rest

    go : Nat -> Double -> List Double -> Nat
    go _ _ [] = lastPossible 0 0 ps
    go k acc (p :: rest) = if p > 0 && r < acc + p then k else go (S k) (acc + p) rest

||| The amplitudes of the other m qudits after the qudit on wire w (of m + 1) was found in |k>,
||| an outcome that had probability prob.
export
collapse : (d : Nat) -> (m : Nat) -> (w : Nat) -> (k : Nat) -> (prob : Double) ->
           Vect (power d (S m)) (Vect 1 (Complex Double)) -> Matrix (power d m) 1
collapse d m w k prob amps = map (\s => [rescale (amplitudeOf (withDigit (finToNat s)))]) range
  where
    low : Nat
    low = power d (minus m w)

    -- basis state s of the m qudits, with digit k put back on wire w
    withDigit : Nat -> Nat
    withDigit s = integerToNat ((natToInteger s `div` natToInteger low) * natToInteger (d * low)
                                + natToInteger (k * low) + (natToInteger s `mod` natToInteger low))

    amplitudeOf : Nat -> Complex Double
    amplitudeOf r = case natToFin r (power d (S m)) of
                      Just f => head (index f amps)
                      Nothing => 0

    rescale : Complex Double -> Complex Double
    rescale a = (realPart a / sqrt prob) :+ (imagPart a / sqrt prob)

--------------------------------------------------------------------------------------------------
-- Block 1: append to the end of Qimaera/Lib.idr
--------------------------------------------------------------------------------------------------
{-
||| State of the qudit simulator: the amplitudes of the d^n basis
||| states, the unitary built since the amplitudes were last updated, the handles in position
||| order and a counter for fresh handles. Same visibility as SimulatedOpOf.
export
data QuditSimulatedOpOf : (qubit : Type) -> (d : Nat) -> Nat -> Type where
  MkQuditSimulatedOp : {n : Nat} -> Matrix (power d n) 1 -> Matrix (power d n) (power d n) -> Vect n qubit -> Nat -> QuditSimulatedOpOf qubit d n
-}

--------------------------------------------------------------------------------------------------
-- Block 2: append to the end of Qimaera/Lib/QuantumOp.idr
--------------------------------------------------------------------------------------------------
{-
||| Qudit proof of concept: add p qudits in |0> to a state of the qudit simulator, 
||| with fresh handles for them. It is here because only this module can create handles.
export
newQuditsSimulatedUST : {d : Nat} -> (p : Nat) ->
  UStateT (QuditSimulatedOpOf Qubit d n) (QuditSimulatedOpOf Qubit d (n + p)) (LVect p Qubit)
newQuditsSimulatedUST {d} p = mkUST (grow p)
  where
    zeroKet : (k : Nat) -> Matrix k 1
    zeroKet Z = []
    zeroKet (S k) = [1] :: replicate k [0]

    grow : (q : Nat) -> (1 _ : QuditSimulatedOpOf Qubit d m) -> LPair (QuditSimulatedOpOf Qubit d (m + q)) (LVect q Qubit)
    grow q (MkQuditSimulatedOp amps un v counter) =
      let (handles # (v', counter')) = newQubitsPointers q counter v in
      MkQuditSimulatedOp (rewrite multPowerPowerPlus d m q in amps `tensorProductAny` zeroKet (power d q))
                         (rewrite multPowerPowerPlus d m q in un `tensorProductAny` matrixId (power d q))
                         (v ++ v') counter' # handles
-}

--------------------------------------------------------------------------------------------------
-- Block 3: the simulator. Uncomment once blocks 1 and 2 are in place.
--------------------------------------------------------------------------------------------------
{-
||| The state of the qudit simulator. Its handles are Qubits, but each stands for a qudit of
||| dimension d.
public export
QuditSimulatedOp : Nat -> Nat -> Type
QuditSimulatedOp d = QuditSimulatedOpOf Qubit d

||| The unitary held by a state, such as one that buildUnitary returns.
export
quditUnitary : (1 _ : QuditSimulatedOp d n) -> Matrix (power d n) (power d n)
quditUnitary (MkQuditSimulatedOp _ u _ _) = u

||| Multiply the gate g, on the wires of qs, into the unitary built so far.
gateOn : {d : Nat} -> {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> Matrix (power d i) (power d i) ->
         (1 _ : QuditSimulatedOp d n) -> LPair (QuditSimulatedOp d n) (LVect i Qubit)
gateOn qs g (MkQuditSimulatedOp amps u v c) =
  let qs' # ids = distributeDupedLVectVect qs in
  MkQuditSimulatedOp amps (applyUMBase {n} {i} d (positions v ids) g `matrixMult` u) v c # qs'

||| The same with g controlled by cs: it acts when all of them are |1>.
controlledOn : {d : Nat} -> {n : Nat} -> {k : Nat} -> {i : Nat} -> (1 _ : LVect k Qubit) -> (1 _ : LVect i Qubit) ->
               Matrix (power d i) (power d i) -> (1 _ : QuditSimulatedOp d n) -> LPair (QuditSimulatedOp d n) (LVect (k + i) Qubit)
controlledOn cs ts g (MkQuditSimulatedOp amps u v c) =
  let cs' # cids = distributeDupedLVectVect cs in
  let ts' # tids = distributeDupedLVectVect ts in
  MkQuditSimulatedOp amps (multiControlledQUM {n} {i} {k} d (positions v cids) 1 (positions v tids) g `matrixMult` u) v c # (cs' ++ ts')

||| Run act from the same state with nothing built yet, and multiply the inverse of what it
||| builds into the unitary built so far.
invertOn : {d : Nat} -> {n : Nat} -> (1 _ : UStateT (QuditSimulatedOp d n) (QuditSimulatedOp d n) a) ->
           (1 _ : QuditSimulatedOp d n) -> LPair (QuditSimulatedOp d n) a
invertOn act (MkQuditSimulatedOp amps u v c) =
  let (MkQuditSimulatedOp _ w _ _) # x = runUStateT (MkQuditSimulatedOp amps (matrixId (power d n)) v c) act in
  MkQuditSimulatedOp amps (adjoint w `matrixMult` u) v c # x

||| Run two actions on disjoint qudits, one after the other.
parallelOn : (1 _ : UStateT (QuditSimulatedOp d n) (QuditSimulatedOp d n) (LVect i Qubit)) ->
             (1 _ : UStateT (QuditSimulatedOp d n) (QuditSimulatedOp d n) (LVect j Qubit)) ->
             (1 _ : QuditSimulatedOp d n) -> LPair (QuditSimulatedOp d n) (LVect (i + j) Qubit)
parallelOn a b st =
  let st1 # xs = runUStateT st a in
  let st2 # ys = runUStateT st1 b in
  st2 # (xs ++ ys)

||| buildUnitary: run f on n fresh qudits; the state returned holds the unitary f builds.
buildOn : {d : Nat} -> {n : Nat} ->
          ((1 _ : LVect n Qubit) -> UStateT (QuditSimulatedOp d n) (QuditSimulatedOp d n) (LVect n Qubit)) -> QuditSimulatedOp d n
buildOn f =
  let st # qs = runUStateT (MkQuditSimulatedOp [[1]] [[1]] [] 0) (newQuditsSimulatedUST n >>= f) in
  let () = discardq qs in
  st

||| UnitaryOp for qudits: H is the Fourier transform on Z_d, P p puts the phase e^(ip) on |1>,
||| CNOT is SUM, and controls act on |1>.
export
{d : Nat} -> UnitaryOp (QuditSimulatedOpOf Qubit d) where
  applyUnitary qs u = mkUST (gateOn qs (unitaryToQuditUM d u))
  applyUnitaryOwn qs (MkQuditSimulatedOp _ u _ _) = mkUST (gateOn qs u)
  applyControlledOwn c ts (MkQuditSimulatedOp _ u _ _) = mkUST (controlledOn [c] ts u)
  adjointUST act = mkUST (invertOn act)
  applyParallel a b = mkUST (parallelOn a b)
  applyH q = mkUST (gateOn [q] (asPow1 d (gateF d)))
  applyP p q = mkUST (gateOn [q] (asPow1 d (phaseOn1 d p)))
  applyCNOT c q = mkUST (gateOn [c, q] (sum2CorePow d))
  applyMultipleControlledOwn cs ts (MkQuditSimulatedOp _ u _ _) = mkUST (controlledOn cs ts u)
  buildUnitary f = buildOn f
  multipleControlUST cs ts pattern = mkUST (controlledOn cs ts (quditUnitary (buildOn pattern)))

||| applyUST: run the action, then apply the unitary it built to the amplitudes.
applyUSTOn : {d : Nat} -> {n : Nat} -> (1 _ : UStateT (QuditSimulatedOp d n) (QuditSimulatedOp d n) (LVect i Qubit)) ->
             (1 _ : QuditSimulatedOp d n) -> R (LPair (QuditSimulatedOp d n) (LVect i Qubit))
applyUSTOn act st =
  let (MkQuditSimulatedOp amps u v c) # qs = runUStateT st act in
  pure1 (MkQuditSimulatedOp (u `matrixMult` amps) (matrixId (power d n)) v c # qs)

||| The wire of handle q.
wireOf : (1 _ : QuditSimulatedOp d n) -> (1 _ : Qubit) -> LFstPair (LPair (QuditSimulatedOp d n) Qubit) Nat
wireOf (MkQuditSimulatedOp amps u v c) q =
  let q' # k = qubitToNatPair q in
  (MkQuditSimulatedOp amps u v c # q') # listIndexN v k

||| Measure the qudit on wire w in the computational basis, and remove it.
measureWire : {d : Nat} -> {m : Nat} -> (w : Nat) -> (1 _ : QuditSimulatedOp d (S m)) -> R (LFstPair (QuditSimulatedOp d m) Nat)
measureWire w (MkQuditSimulatedOp amps u v c) = do
  r <- liftIO1 randomIO
  pure1 (outcomeIs (pickOutcome probabilities r))
  where
    state : Matrix (power d (S m)) 1
    state = u `matrixMult` amps

    probabilities : List Double
    probabilities = outcomeProbabilities d (S m) w state

    outcomeIs : Nat -> LFstPair (QuditSimulatedOp d m) Nat
    outcomeIs k = MkQuditSimulatedOp (collapse d m w k (fromMaybe 0 (getAt k probabilities)) state)
                                     (matrixId (power d m)) (removeElem v w) c # k

||| Measure the qudits qs one after the other; the outcomes are 0 .. d-1.
measureOn : {d : Nat} -> {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) ->
            (1 _ : QuditSimulatedOp d (i + n)) -> R (LPair (QuditSimulatedOp d n) (Vect i Nat))
measureOn [] st = pure1 (st # [])
measureOn {i = S i'} (q :: qs) st =
  let (st' # q') # w = wireOf st q in
  let () = discardq [q'] in do
    (st'' # k) <- measureWire {m = i' + n} w st'
    (st3 # ks) <- measureOn qs st''
    case ks of
      [] => pure1 (st3 # [k])
      (k' :: ks') => pure1 (st3 # (k :: k' :: ks'))

||| Measure qudits and get the full outcomes 0 .. d-1 (QuantumOp's measure can only return a Bool).
export
measureQudits : {d : Nat} -> {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) ->
                QStateT (QuditSimulatedOp d (i + n)) (QuditSimulatedOp d n) (Vect i Nat)
measureQudits qs = MkQST (measureOn qs)

||| Run a qudit program from no qudits back to none.
export
runQudits : {d : Nat} -> QStateT (QuditSimulatedOp d 0) (QuditSimulatedOp d 0) (Vect n a) -> IO (Vect n a)
runQudits s = LIO.run (do
  ((MkQuditSimulatedOp _ _ _ _) # v) <- runQStateT (MkQuditSimulatedOp [[1]] [[1]] [] 0) s
  case v of
    [] => pure []
    (x :: xs) => pure (x :: xs))

||| QuantumOp for qudits. measure returns True when the qudit is found in |1>; this agrees with
||| controls acting on |1>. measureQudits gives the full outcome.
export
{d : Nat} -> QuantumOp (QuditSimulatedOpOf Qubit d) where
  newQubits p = MkQST (\st => pure1 (runUStateT st (newQuditsSimulatedUST p)))
  applyUST act = MkQST (applyUSTOn act)
  applyUnitaryDirectly u qs = MkQST (applyUSTOn (applyUnitary qs u))
  measure qs = MkQST (\st => do (st' # ks) <- measureOn qs st
                                case ks of
                                  [] => pure1 (st' # [])
                                  (k :: ks') => pure1 (st' # map (== 1) (k :: ks')))
  run = runQudits
  -- QuantumOp's default definitions of these three do not typecheck for this implementation
  applyHQ q = MkQST (applyUSTOn (applyH q))
  applyPQ p q = MkQST (applyUSTOn (applyP p q))
  applyCNOTQ c q = MkQST (applyUSTOn (applyCNOT c q))

--------------------------------------------------------------------------------------------------
-- Demo
--------------------------------------------------------------------------------------------------

||| On qutrits: prepare (|00> + |11> + |22>) / sqrt 3 with H and CNOT, and measure both.
export
qutritBellPair : QStateT (QuditSimulatedOp 3 0) (QuditSimulatedOp 3 0) (Vect 2 Nat)
qutritBellPair = do
  [a, b] <- newQubits {t = QuditSimulatedOp 3} 2
  [a1] <- applyHQ a
  [a2, b1] <- applyCNOTQ a1 b
  measureQudits [a2, b1]

||| Measures the qutrit Bell pair 300 times: the two outcomes always agree, and each of 0, 1 and 2
||| comes up about 100 times.
export
quditDemo : IO ()
quditDemo = do
  outcomes <- traverse (\_ => runQudits qutritBellPair) (replicate 300 ())
  putStrLn $ "qutrit Bell pair, measured 300 times: the outcomes agreed "
             ++ show (length (filter agree outcomes)) ++ " times; the first qutrit gave "
             ++ show (count 0 outcomes) ++ " x 0, " ++ show (count 1 outcomes) ++ " x 1, "
             ++ show (count 2 outcomes) ++ " x 2"
  where
    agree : Vect 2 Nat -> Bool
    agree [x, y] = x == y

    count : Nat -> List (Vect 2 Nat) -> Nat
    count k = length . filter (\o => head o == k)
-}
