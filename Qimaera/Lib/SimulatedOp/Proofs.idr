module Qimaera.Lib.SimulatedOp.Proofs

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


||| The unitary of a state.
public export
unitaryOf : SimulatedOp n -> Unitary n
unitaryOf (MkSimulatedOp _ u _ _) = u

||| u keeps the live handles, whatever they are.
public export
KeepsFrame : {n : Nat} -> {a : Type} -> UStateT (SimulatedOp n) (SimulatedOp n) a -> Type
KeepsFrame u = (v : Vect n Qubit) -> KeepsU (Frame v) (Frame v) u

||| A computation that changes only the unitary of every state keeps the live handles.
keepsFrom : {n : Nat} -> {a : Type} -> {u : UStateT (SimulatedOp n) (SimulatedOp n) a}
         -> ((st : Matrix (power 2 n) 1) -> (un : Unitary n) -> (v : Vect n Qubit) -> (c : Nat)
             -> (u' : Unitary n ** (r : a ** runUStateT (MkSimulatedOp st un v c) u = (MkSimulatedOp st u' v c # r))))
         -> KeepsFrame u
keepsFrom runs v = MkKeepsU keep
  where
    keep : (s : SimulatedOp n) -> Frame v s -> Frame v (fst (unLPair (runUStateT s u)))
    keep (MkSimulatedOp st un w c) ok with (runs st un w c)
      _ | (u' ** r ** eq) = replace {p = \x => Frame v (fst (unLPair x))} (sym eq) ok

||| The other operations that apply a gate do so as applyUnitary does: at the positions of their handles, giving
||| them back. checkPasses and applySafeIsApply turn each into apply, as in applyUnitaryApplies.
export
applyUnitaryOwnRuns : {n, i : Nat} -> (lv : LVect i Qubit) -> (own : SimulatedOp i)
                   -> (st : Matrix (power 2 n) 1) -> (un : Unitary n) -> (v : Vect n Qubit) -> (c : Nat)
                   -> runUStateT (MkSimulatedOp st un v c) (applyUnitaryOwn {t = SimulatedOp} lv own)
                      = (MkSimulatedOp st (fstLFP (applySafe (unitaryOf own) un (positions v (lids lv)))) v c # lv)
applyUnitaryOwnRuns lv (MkSimulatedOp _ u' _ _) st un v c with (applySafe u' un (positions v (lids lv))) proof eq
  _ | (unew # io) = rewrite distributeIs lv in rewrite eq in Refl

export
applyControlledOwnRuns : {n, i : Nat} -> (q : Qubit) -> (ts : LVect i Qubit) -> (own : SimulatedOp i)
                      -> (st : Matrix (power 2 (S n)) 1) -> (un : Unitary (S n)) -> (v : Vect (S n) Qubit) -> (c : Nat)
                      -> runUStateT (MkSimulatedOp st un v c) (applyControlledOwn {t = SimulatedOp} q ts own)
                         = (MkSimulatedOp st (fstLFP (applySafe (controlled (unitaryOf own)) un
                                                                (positions v (lids (q :: ts))))) v c # (q :: ts))
applyControlledOwnRuns q ts (MkSimulatedOp _ u' _ _) st un v c
  with (applySafe (controlled u') un (positions v (lids (q :: ts)))) proof eq
  _ | (unew # io) = rewrite qubitToNatPairIs q in rewrite distributeIs ts in rewrite eq in Refl

export
applyMultipleControlledOwnRuns : {n, i, k : Nat} -> (cs : LVect (S k) Qubit) -> (ts : LVect i Qubit)
                              -> (own : SimulatedOp i) -> (st : Matrix (power 2 (S k + n)) 1)
                              -> (un : Unitary (S k + n)) -> (v : Vect (S k + n) Qubit) -> (c : Nat)
                              -> runUStateT (MkSimulatedOp st un v c)
                                            (applyMultipleControlledOwn {t = SimulatedOp} {n} cs ts own)
                                 = (MkSimulatedOp st (fstLFP (applySafe (multipleControlled (S k) (unitaryOf own)) un
                                                                        (positions v (lids cs ++ lids ts))))
                                                  v c # (cs ++ ts))
applyMultipleControlledOwnRuns (q :: cs) ts (MkSimulatedOp _ u' _ _) st un v c
  with (applySafe (multipleControlled (S k) u') un (positions v (lids (q :: cs) ++ lids ts))) proof eq
  _ | (unew # io) = rewrite distributeIs (q :: cs) in rewrite distributeIs ts in rewrite eq in Refl

export
controlUSTRuns : {n, i : Nat} -> (q : Qubit) -> (locs : LVect i Qubit)
              -> (pat : (1 _ : LVect i Qubit) -> UStateT (SimulatedOp i) (SimulatedOp i) (LVect i Qubit))
              -> (st : Matrix (power 2 n) 1) -> (un : Unitary n) -> (v : Vect n Qubit) -> (c : Nat)
              -> runUStateT (MkSimulatedOp st un v c) (controlUST {t = SimulatedOp} q locs pat)
                 = (MkSimulatedOp st (fstLFP (applySafe (controlled (unitaryOf (buildUnitary {t = SimulatedOp} pat))) un
                                                        (positions v (lids (q :: locs))))) v c # (q :: locs))
controlUSTRuns q locs pat st un v c with (buildUnitary' {n = i} pat)
  _ | (MkSimulatedOp _ u' _ _) with (applySafe (controlled u') un (positions v (lids (q :: locs)))) proof eq
    _ | (unew # io) = rewrite qubitToNatPairIs q in rewrite distributeIs locs in rewrite eq in Refl