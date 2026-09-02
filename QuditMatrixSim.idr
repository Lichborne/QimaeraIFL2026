module QuditMatrixSim

import Matrix
import Data.Vect
import Data.Nat
import Complex
import Lemmas
import QuantumOp
import UnitaryLinear
import UStateT
import LinearTypes
import Decidable.Equality
import QuditMatrix

%default total

||| Base-dependent simulation helpers for QuditUM.
||| Used to implement UnitaryOp (QuditUM base); the Qubit type is treated as a wire index.
||| See the UnitaryMatrix simulator for the base-2 (qubit) intuition.

||| "fromUtoQUM" converts a Unitary n circuit into a QuditUM base n matrix.
export
fromUtoQUM : {n : Nat} -> (base : Nat) -> Unitary n -> QuditUM base n
fromUtoQUM base un = unitaryToQuditUM base un

||| "applyUnitaryOwnQUMSim'" lifts an i-qudit unitary to n wires and left-multiplies it into the current unitary.
applyUnitaryOwnQUMSim' :
  {base : Nat} -> {n : Nat} -> {i : Nat} ->
  (1 _  : LVect i Qubit) ->
  (1 _  : QuditUM base i) ->
  (1 _  : QuditUM base n) ->
  LPair (QuditUM base n) (LVect i Qubit)
applyUnitaryOwnQUMSim' {base} {n} {i} qubits umi umn =
  let (umi1, umi2) = dupMatrixCD umi in
  let (umnFree, vac) = dupMatrixCD umn in
  let lq # q = distributeDupedLVectVect qubits in
  let lifted : QuditUM base n = applyUMBase {n} {i} base q umi1 in
  let uOut = matrixMult lifted umnFree in
    uOut # lq

||| "applyUnitaryOwnQUMSim" packages "applyUnitaryOwnQUMSim'" as a UStateT action.
export
applyUnitaryOwnQUMSim :
  {base : Nat} -> {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) ->
  (1 _ : QuditUM base i) ->
  UStateT (QuditUM base n) (QuditUM base n) (LVect i Qubit)
applyUnitaryOwnQUMSim qubits ui =
  MkUST (applyUnitaryOwnQUMSim' qubits ui)

||| "applyUnitaryQUMSim'" lifts a Unitary i circuit to n wires (via applySafe) and left-multiplies it into the current unitary.
applyUnitaryQUMSim' :
  {base : Nat} -> {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) ->
  Unitary i ->
  (1 _ : QuditUM base n) ->
  LPair (QuditUM base n) (LVect i Qubit)
applyUnitaryQUMSim' {base} {n} {i} qubits ui umn =
  let lq # q = distributeDupedLVectVect qubits in
  let (umnFree, vac) = dupMatrixCD umn in
  let ui2n # _ = applySafe ui (IdGate {n=n}) q in
  let umi2n : QuditUM base n = fromUtoQUM {n} base ui2n in
  let uOut = matrixMult umi2n umnFree in
    uOut # lq

||| "applyUnitaryQUMSim" packages "applyUnitaryQUMSim'" as a UStateT action.
export
applyUnitaryQUMSim :
  {base : Nat} -> {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) ->
  Unitary i ->
  UStateT (QuditUM base n) (QuditUM base n) (LVect i Qubit)
applyUnitaryQUMSim qubits ui =
  MkUST (applyUnitaryQUMSim' qubits ui)

||| "applyHQUMSim'" applies a single-qudit Fourier gate F_base on one wire and left-multiplies it into the current unitary.
applyHQUMSim' :
  {base : Nat} -> {n : Nat} ->
  (1 _ : Qubit) ->
  (1 _ : QuditUM base n) ->
  LPair (QuditUM base n) (LVect 1 Qubit)
applyHQUMSim' {base} {n} qubit umn =
  let (q, k) = qubitToNatPair qubit in
  let (umnFree, vac) = dupMatrixCD umn in
  let g1 : Matrix (power base 1) (power base 1) = asPow1 base (gateF base) in
  let left : QuditUM base n = applyUMBase {n} {i = 1} base [k] g1 in
    matrixMult left umnFree # [q]

||| "applyHQUMSim" packages "applyHQUMSim'" as a UStateT action.
export
applyHQUMSim :
  {base : Nat} -> {n : Nat} ->
  (1 _ : Qubit) ->
  UStateT (QuditUM base n) (QuditUM base n) (LVect 1 Qubit)
applyHQUMSim qubit = MkUST (applyHQUMSim' qubit)

||| "applyPQUMSim'" applies a single-qudit phase-on-|1⟩ gate on one wire and left-multiplies it into the current unitary.
applyPQUMSim' :
  {base : Nat} -> {n : Nat} ->
  (1 _ : Qubit) -> (p : Double) ->
  (1 _ : QuditUM base n) ->
  LPair (QuditUM base n) (LVect 1 Qubit)
applyPQUMSim' {base} {n} qubit p umn =
  let (q, k) = qubitToNatPair qubit in
  let (umnFree, vac) = dupMatrixCD umn in
  let g1 : Matrix (power base 1) (power base 1) = asPow1 base (phaseOn1 base p) in
  let left : QuditUM base n = applyUMBase {n} {i = 1} base [k] g1 in
    matrixMult left umnFree # [q]

||| "applyPQUMSim" packages "applyPQUMSim'" as a UStateT action.
export
applyPQUMSim :
  {base : Nat} -> {n : Nat} ->
  (p : Double) -> (1 _ : Qubit) ->
  UStateT (QuditUM base n) (QuditUM base n) (LVect 1 Qubit)
applyPQUMSim p qubit = MkUST (applyPQUMSim' qubit p)

||| "applyCNOTQUMSim'" applies the two-qudit SUM gate on wires (control,target) and left-multiplies it into the current unitary.
applyCNOTQUMSim' :
  {base : Nat} -> {n : Nat} ->
  (1 _ : Qubit) -> (1 _ : Qubit) ->
  (1 _ : QuditUM base n) ->
  LPair (QuditUM base n) (LVect 2 Qubit)
applyCNOTQUMSim' {base} {n} c t umn =
  let (cWire, i) = qubitToNatPair c in
  let (tWire, j) = qubitToNatPair t in
  let (umnFree, vac) = dupMatrixCD umn in
  let g2 : Matrix (power base 2) (power base 2) = sum2CorePow base in
  let left : QuditUM base n = applyUMBase {n} {i = 2} base [i, j] g2 in
    matrixMult left umnFree # [cWire, tWire]

||| "applyCNOTQUMSim" packages "applyCNOTQUMSim'" as a UStateT action.
export
applyCNOTQUMSim :
  {base : Nat} -> {n : Nat} ->
  (1 _ : Qubit) -> (1 _ : Qubit) ->
  UStateT (QuditUM base n) (QuditUM base n) (LVect 2 Qubit)
applyCNOTQUMSim c t = MkUST (applyCNOTQUMSim' c t)

||| "adjointUSTQUMSim'" inverts a UStateT-built unitary via adjoint and left-multiplies it into the current unitary.
adjointUSTQUMSim' :
  {base : Nat} -> {n : Nat} ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LVect i Qubit)) ->
  (1 _ : QuditUM base n) ->
  LPair (QuditUM base n) (LVect i Qubit)
adjointUSTQUMSim' {base} {n} ust um =
  let un # lvOut = runUStateT (idQU {base} {n}) ust in
  let (uni1, vac) = dupMatrixCD un in
  let (umFree, vac) = dupMatrixCD um in
  let invu = adjoint uni1 in
  let unew = matrixMult invu umFree in
    unew # lvOut

||| "adjointUSTQUMSim" packages "adjointUSTQUMSim'" as a UStateT action.
export
adjointUSTQUMSim :
  {base : Nat} -> {n : Nat} ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LVect i Qubit)) ->
  UStateT (QuditUM base n) (QuditUM base n) (LVect i Qubit)
adjointUSTQUMSim ust = MkUST (adjointUSTQUMSim' ust)

||| "multiControlledQUM" builds an n-wire controlled unitary from a small ui,
||| enabled when all controls equal val, acting on the targets wires.
public export
multiControlledQUM :
  {n : Nat} -> {i : Nat} -> {k : Nat} ->
  (base : Nat) ->
  (controls : Vect k Nat) -> (val : Nat) ->
  (targets  : Vect i Nat) ->
  Matrix (power base i) (power base i) ->
  Matrix (power base n) (power base n)
multiControlledQUM {n} {i} {k} base controls val targets ui =
  buildMatrixNatQudit (power base n) (power base n) entry
  where
    entry : Nat -> Nat -> Complex Double
    entry r c =
      if controlsMatch base controls val c then
        if sameOnOtherQuditsBase {n} {i} base targets r c then
          let rr = extractSubIndexNewBase {n} {i} base targets r
              cc = extractSubIndexNewBase {n} {i} base targets c
          in matIndexNatDefQudit 0 rr cc ui
        else 0
      else
        case decEq r c of
          Yes _ => 1
          No  _ => 0

||| "applyControlledQUMSim'" applies an i-wire unitary controlled by a single wire being 1.
applyControlledQUMSim' :
  {base : Nat} -> {n : Nat} -> {i : Nat} ->
  (1 control : Qubit) ->
  (1 targets : LVect i Qubit) ->
  (1 ownUnitary : QuditUM base i) ->
  (1 _ : QuditUM base (S n)) ->
  LPair (QuditUM base (S n)) (LVect (S i) Qubit)
applyControlledQUMSim' {base} {n} {i} c ts umi umsn =
  let (umi1, vac1) = dupMatrixCD umi in
  let (umsnFree, vac) = dupMatrixCD umsn in
  let (cWire, k) = qubitToNatPair c in
  let (tsLV # ks) = distributeDupedLVectVect ts in
  let full : QuditUM base (S n) =
        multiControlledQUM {n = S n} {i} {k = 1} base [k] 1 ks umi1
  in matrixMult full umsnFree # (cWire :: tsLV)

||| "applyControlledQUMSim" packages "applyControlledQUMSim'" as a UStateT action.
export
applyControlledQUMSim :
  {base : Nat} -> {n : Nat} -> {i : Nat} ->
  (1 control : Qubit) ->
  (1 targets : LVect i Qubit) ->
  (1 ownUnitary : QuditUM base i) ->
  UStateT (QuditUM base (S n)) (QuditUM base (S n)) (LVect (S i) Qubit)
applyControlledQUMSim c ts umi = MkUST (applyControlledQUMSim' c ts umi)

||| "applyMultipleControlledOwnQUMSim'" applies an i-wire unitary controlled by multiple wires all being 1.
applyMultipleControlledOwnQUMSim' :
  {base : Nat} -> {n : Nat} -> {i : Nat} -> {k : Nat} ->
  (1 controls : LVect (S k) Qubit) ->
  (1 targets  : LVect i Qubit) ->
  (1 ownUnitary : QuditUM base i) ->
  (1 _ : QuditUM base ((S k) + n)) ->
  LPair (QuditUM base ((S k) + n)) (LVect ((S k) + i) Qubit)
applyMultipleControlledOwnQUMSim' {base} {n} {i} {k} cs ts umi umsn =
  let (umi1, vac1) = dupMatrixCD umi in
  let (umsnFree, vac2) = dupMatrixCD umsn in
  let lvControls # controls = distributeDupedLVectVect cs in
  let tsLV # targets = distributeDupedLVectVect ts in
  let full : QuditUM base ((S k) + n) =
        multiControlledQUM {n = (S k + n)} {i} {k = (S k)} base controls 1 targets umi1
  in matrixMult full umsnFree # (lvControls ++ tsLV)

||| "applyMultipleControlledOwnQUMSim" packages "applyMultipleControlledOwnQUMSim'" as a UStateT action.
export
applyMultipleControlledOwnQUMSim :
  {base : Nat} -> {n : Nat} -> {i : Nat} -> {k : Nat} ->
  (1 controls : LVect (S k) Qubit) ->
  (1 targets  : LVect i Qubit) ->
  (1 ownUnitary : QuditUM base i) ->
  UStateT (QuditUM base ((S k) + n)) (QuditUM base ((S k) + n)) (LVect ((S k) + i) Qubit)
applyMultipleControlledOwnQUMSim cs ts umi =
  MkUST (applyMultipleControlledOwnQUMSim' cs ts umi)

||| "applyParallelQUMSim'" composes two UStateT programs in sequence and concatenates their wire outputs.
applyParallelQUMSim' :
  {base : Nat} -> {n : Nat} -> {i : Nat} -> {j : Nat} ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LVect i Qubit)) ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LVect j Qubit)) ->
  (1 _ : QuditUM base n) ->
  LPair (QuditUM base n) (LVect (i + j) Qubit)
applyParallelQUMSim' {base} {n} ust1 ust2 umn =
  let (unew1 # lvecti) = runUStateT (idQU {base} {n}) ust1 in
  let (unew2 # lvectj) = runUStateT (idQU {base} {n}) ust2 in
  let (unew1Free, vac1) = dupMatrixCD unew1 in
  let (unew2Free, vac2) = dupMatrixCD unew2 in
  let (umnFree, vac3) = dupMatrixCD umn in
  let unewest = matrixMult unew1Free umnFree in
  let uOut    = matrixMult unew2Free unewest in
    uOut # (lvecti ++ lvectj)

||| "applyParallelQUMSim" packages "applyParallelQUMSim'" as a UStateT action.
export
applyParallelQUMSim :
  {base : Nat} -> {n : Nat} -> {i : Nat} -> {j : Nat} ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LVect i Qubit)) ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LVect j Qubit)) ->
  UStateT (QuditUM base n) (QuditUM base n) (LVect (i + j) Qubit)
applyParallelQUMSim ust1 ust2 = MkUST (applyParallelQUMSim' ust1 ust2)

||| "runQUMSim" runs a UStateT program starting from an existing QuditUM base n.
public export
runQUMSim :
  {base : Nat} -> {n : Nat} -> {i : Nat} ->
  (1 _ : QuditUM base n) ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LVect i Qubit)) ->
  LPair (QuditUM base n) (LVect i Qubit)
runQUMSim un ust = runUStateT un ust

||| "runSplitQUMSim" runs a split-output UStateT program and returns both wire lists.
public export
runSplitQUMSim :
  {base : Nat} -> {n : Nat} -> {i : Nat} -> {j : Nat} ->
  (1 _ : QuditUM base n) ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LPair (LVect i Qubit) (LVect j Qubit))) ->
  LPair (QuditUM base n) (LPair (LVect i Qubit) (LVect j Qubit))
runSplitQUMSim un ust = runUStateT un ust

||| "combineAbsQUM'" runs a split-output program and concatenates its two wire lists.
private
combineAbsQUM' :
  {base : Nat} -> {n : Nat} -> {i : Nat} -> {j : Nat} ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LPair (LVect i Qubit) (LVect j Qubit))) ->
  (1 _ : QuditUM base n) ->
  LPair (QuditUM base n) (LVect (i + j) Qubit)
combineAbsQUM' ust ui =
  let (Builtin.(#) opOut (lvect # rvect)) = runSplitQUMSim ui ust in
    (Builtin.(#) opOut (LinearTypes.(++) lvect rvect))

||| "combineAbsQUMSim" packages "combineAbsQUM'" as a UStateT action.
export
combineAbsQUMSim :
  {base : Nat} -> {n : Nat} -> {i : Nat} -> {j : Nat} ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LPair (LVect i Qubit) (LVect j Qubit))) ->
  UStateT (QuditUM base n) (QuditUM base n) (LVect (i + j) Qubit)
combineAbsQUMSim q = MkUST (combineAbsQUM' q)

||| "controlMUSTQUM'" builds a target unitary from a pattern and applies it under multi-control (controls==1) on the chosen locations.
controlMUSTQUM' :
  {base : Nat} -> {n : Nat} -> {i : Nat} -> {j : Nat} ->
  (1 controls  : LVect i Qubit) ->
  (1 locations : LVect j Qubit) ->
  (targetPattern : ((1 _ : LVect j Qubit) ->
                    UStateT (QuditUM base j) (QuditUM base j) (LVect j Qubit))) ->
  (1 _ : QuditUM base n) ->
  LPair (QuditUM base n) (LVect (i + j) Qubit)
controlMUSTQUM' {base} {n} {i} {j} ctrl locs targetP un =
  let u : QuditUM base j = buildQuditUM {n = j} targetP in
  let (unFree, vac) = dupMatrixCD un in
  let lvControls # controls = distributeDupedLVectVect ctrl in
  let qs # ts = distributeDupedLVectVect locs in
  let ucFull : QuditUM base n =
        multiControlledQUM {n} {i = j} {k = i} base controls 1 ts u
  in matrixMult ucFull unFree # (lvControls ++ qs)

||| "controlMUSTQUMSim" packages "controlMUSTQUM'" as a UStateT action.
export
controlMUSTQUMSim :
  {base : Nat} -> {n : Nat} -> {i : Nat} -> {j : Nat} ->
  (1 controls  : LVect i Qubit) ->
  (1 locations : LVect j Qubit) ->
  (targetPattern : ((1 _ : LVect j Qubit) ->
                    UStateT (QuditUM base j) (QuditUM base j) (LVect j Qubit))) ->
  UStateT (QuditUM base n) (QuditUM base n) (LVect (i + j) Qubit)
controlMUSTQUMSim ctrl loc targetP = MkUST (controlMUSTQUM' ctrl loc targetP)