module Qimaera.Lib.ConcreteImplementations.SimulatedOp.Proofs

import Data.Vect
import Data.Vect.Elem
import Data.Vect.Quantifiers
import Utilities.Injection
import Utilities.LinearTypes
import Utilities.UnitaryLinear
import Utilities.Matrix
import Qimaera.Lib
import Qimaera.Lib.UStateT.Proofs
import Qimaera.Lib.QuantumOp
import Qimaera.Lib.QuantumOp.Proofs
import Qimaera.Lib.ConcreteImplementations.SimulatedOp

%default total

||| A minimal check that SimulatedOp does what the abstract argument assumes of an operation.


||| On a state with handles v, applyUnitary applies its gate at the right positions, leaves the rest as is, and gives the handles back.
export
applyUnitaryRuns : {n, i : Nat} -> (lv : LVect i Qubit) -> (ui : Unitary i)
                -> (st : Matrix (power 2 n) 1) -> (un : Unitary n) -> (v : Vect n Qubit) -> (c : Nat)
                -> runUStateT (MkSimulatedOp st un v c) (applyUnitary {t = SimulatedOp} lv ui)
                   = (MkSimulatedOp st (fstLFP (applySafe ui un (positions v (lids lv)))) v c # lv)
applyUnitaryRuns lv ui st un v c with (applySafe ui un (positions v (lids lv))) proof eq
  _ | (unew # io) = rewrite distributeIs lv in rewrite eq in Refl

||| If the handles are live and their ids pairwise different, the gate is applied as by apply.
export
applyUnitaryApplies : {n, i : Nat} -> (lv : LVect i Qubit) -> (ui : Unitary i)
                   -> (st : Matrix (power 2 n) 1) -> (un : Unitary n) -> (v : Vect n Qubit) -> (c : Nat)
                   -> All (\k => Elem k (toVectN v)) (lids lv) -> AllDifferentDec (lids lv)
                   -> (prf : IsInjectiveT n (positions v (lids lv))
                       ** runUStateT (MkSimulatedOp st un v c) (applyUnitary {t = SimulatedOp} lv ui)
                          = (MkSimulatedOp st (apply ui un (positions v (lids lv)) {prf}) v c # lv))
applyUnitaryApplies lv ui st un v c live diff with (checkPasses v (lids lv) live diff)
  _ | (prf ** ok) = (prf ** rewrite sym (applySafeIsApply ui un (positions v (lids lv)) ok) in
                             applyUnitaryRuns lv ui st un v c)

||| The live handles of the state are v.
public export
Frame : Vect n Qubit -> SimulatedOp n -> Type
Frame v (MkSimulatedOp _ _ w _) = w = v

||| So applyUnitary keeps the live handles, and bindKeeps carries this through any computation built from operations that keep them.
export
applyUnitaryKeeps : {n, i : Nat} -> (lv : LVect i Qubit) -> (ui : Unitary i) -> (v : Vect n Qubit)
                 -> KeepsU (Frame v) (Frame v) (applyUnitary {t = SimulatedOp} lv ui)
applyUnitaryKeeps lv ui v = MkKeepsU keep
  where
    keep : (s : SimulatedOp n) -> Frame v s
        -> Frame v (fst (unLPair (runUStateT s (applyUnitary {t = SimulatedOp} lv ui))))
    keep (MkSimulatedOp st un w c) ok =
      replace {p = \r => Frame v (fst (unLPair r))} (sym (applyUnitaryRuns lv ui st un w c)) ok