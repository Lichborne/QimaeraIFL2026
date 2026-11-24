module Qimaera.Lib.QuantumOp.Proofs

import Data.Nat
import Data.Vect
import Data.Vect.Elem
import Data.Vect.Quantifiers
import Utilities.Injection
import Utilities.LinearTypes
import Utilities.UnitaryLinear
import Utilities.Lemmas
import Qimaera.Lib
import Qimaera.Lib.QuantumOp

%default total

||| The library's translation of handles to wires: for live handles whose ids are pairwise
||| different, positions gives wires below n that are pairwise different, so the check in
||| applySafe (decInj) passes (checkPasses), and applySafe then applies the gate exactly as apply,
||| which needs that proof statically (applySafeIsApply). This module is below
||| Qimaera.Lib.QuantumOp, so it can unfold that module's definitions.

private
qid : Qubit -> Nat
qid (MkQubit k) = k

public export
lids : LVect n Qubit -> Vect n Nat
lids [] = []
lids (q :: qs) = qid q :: lids qs

||| The handle utilities give back the handles they are given, with their ids.
public export
qubitToNatPairIs : (q : Qubit) -> qubitToNatPair q = (q # qid q)
qubitToNatPairIs (MkQubit k) = Refl

public export
distributeIs : (lv : LVect n Qubit) -> distributeDupedLVectVect lv = (lv # lids lv)
distributeIs [] = Refl
distributeIs (MkQubit k :: xs) = rewrite distributeIs xs in Refl

eqTrue : (x, k : Nat) -> (x == k) = True -> x = k
eqTrue Z Z _ = Refl
eqTrue (S x) (S k) eq = cong S (eqTrue x k eq)
eqTrue Z (S k) eq = absurd eq
eqTrue (S x) Z eq = absurd eq

eqRefl : (x : Nat) -> (x == x) = True
eqRefl Z = Refl
eqRefl (S x) = eqRefl x

elemNotHead : {k : Nat} -> Elem k (x :: ks) -> (x == k) = False -> Elem k ks
elemNotHead Here eq = absurd (trans (sym eq) (eqRefl k))
elemNotHead (There e) _ = e

listIndexLT : {n, k : Nat} -> (v : Vect n Qubit) -> Elem k (toVectN v) -> LT (listIndexN v k) n
listIndexLT [] e = absurd e
listIndexLT (MkQubit x :: xs) e with (x == k) proof eq
  _ | True = LTESucc LTEZero
  _ | False = LTESucc (listIndexLT xs (elemNotHead e eq))

listIndexInj : {n, j, k : Nat} -> (v : Vect n Qubit) -> Elem j (toVectN v) -> Elem k (toVectN v)
            -> listIndexN v j = listIndexN v k -> j = k
listIndexInj [] ej _ _ = absurd ej
listIndexInj (MkQubit x :: xs) ej ek eq with (x == j) proof pj
  _ | True with (x == k) proof pk
    _ | True = trans (sym (eqTrue x j pj)) (eqTrue x k pk)
    _ | False = absurd eq
  _ | False with (x == k) proof pk
    _ | True = absurd eq
    _ | False = listIndexInj xs (elemNotHead ej pj) (elemNotHead ek pk) (injective eq)

neqLT : {a, b : Nat} -> Not (a = b) -> Either (LT a b) (LT b a)
neqLT {a = Z} {b = Z} ne = absurd (ne Refl)
neqLT {a = Z} {b = S b} _ = Left (LTESucc LTEZero)
neqLT {a = S a} {b = Z} _ = Right (LTESucc LTEZero)
neqLT {a = S a} {b = S b} ne = bimap LTESucc LTESucc (neqLT (\eq => ne (cong S eq)))

positionsSmaller : {n : Nat} -> (v : Vect n Qubit) -> (ks : Vect i Nat) -> All (\k => Elem k (toVectN v)) ks
                -> AllSmallerT (positions v ks) n
positionsSmaller v [] [] = ASNil
positionsSmaller v (k :: ks) (e :: es) = ASSucc (listIndexLT v e) (positionsSmaller v ks es)

positionNotIn : {n, k : Nat} -> (v : Vect n Qubit) -> Elem k (toVectN v)
             -> (ks : Vect i Nat) -> All (\j => Elem j (toVectN v)) ks -> IsDifferentDec k ks
             -> IsDifferentT (listIndexN v k) (positions v ks)
positionNotIn v ek [] [] _ = IsDiffNil
positionNotIn v ek (j :: ks) (ej :: es) (IsDiffSuccDec ne rest) =
  IsDiffSucc (neqLT (\eq => ne (listIndexInj v ek ej eq))) (positionNotIn v ek ks es rest)

positionsDifferent : {n : Nat} -> (v : Vect n Qubit) -> (ks : Vect i Nat) -> All (\k => Elem k (toVectN v)) ks
                  -> AllDifferentDec ks -> AllDifferentT (positions v ks)
positionsDifferent v [] [] AllDiffNilDec = AllDiffNil
positionsDifferent v (k :: ks) (e :: es) (AllDiffSuccDec nk dks) =
  AllDiffSucc (positionNotIn v e ks es nk) (positionsDifferent v ks es dks)

||| For live handles (ids among the live ids) whose ids are pairwise different, the positions
||| satisfy IsInjectiveT n ...
export
positionsInjective : {n : Nat} -> (v : Vect n Qubit) -> (ks : Vect i Nat)
                  -> All (\k => Elem k (toVectN v)) ks -> AllDifferentDec ks -> IsInjectiveT n (positions v ks)
positionsInjective v ks es dks = IsInjectiveSucc (positionsDifferent v ks es dks) (positionsSmaller v ks es)

decYes : (d : Dec p) -> p -> (q ** d = Yes q)
decYes (Yes q) _ = (q ** Refl)
decYes (No no) x = absurd (no x)

||| ... so decInj accepts them, and applySafe applies the gate.
export
checkPasses : {n : Nat} -> (v : Vect n Qubit) -> (ks : Vect i Nat)
           -> All (\k => Elem k (toVectN v)) ks -> AllDifferentDec ks -> (prf ** decInj n (positions v ks) = Yes prf)
checkPasses v ks es dks = decYes (decInj n (positions v ks)) (positionsInjective v ks es dks)

||| When the check passes, applySafe is apply.
export
applySafeIsApply : {i, n : Nat} -> (ui : Unitary i) -> (un : Unitary n) -> (v : Vect i Nat) -> {prf : IsInjectiveT n v}
                -> decInj n v = Yes prf -> fstLFP (applySafe ui un v) = apply ui un v {prf}
applySafeIsApply IdGate un v eq = Refl
applySafeIsApply (H j g) un v eq = rewrite eq in Refl
applySafeIsApply (P p j g) un v eq = rewrite eq in Refl
applySafeIsApply (CNOT c t g) un v eq = rewrite eq in Refl
------------------------------------------------------------------------
-- Fresh identifiers in SimulatedOp.
-- newQubitsPointers gives new qubits the identifiers counter, counter + 1, ... and moves the
-- counter past them, measurement only removes handles, and unitaries change neither (applyCircFresh,
-- and keepsFresh in SimulatedOp/Proofs.idr). So every SimulatedOp state that run reaches satisfies
-- FreshIds: its live identifiers are pairwise different and below its counter.

||| Every identifier in ks is below c.
public export
Below : Nat -> Vect n Nat -> Type
Below c ks = All (\k => LT k c) ks

||| The identifier invariant of a SimulatedOp state with live handles v and counter c.
public export
FreshIds : Vect n Qubit -> Nat -> Type
FreshIds v c = (AllDifferentDec (toVectN v), Below c (toVectN v))

||| run, buildUnitary and runUnitaryOp start from no qubits and counter 0.
export
freshStart : FreshIds [] 0
freshStart = (AllDiffNilDec, [])

||| The identifiers c, c + 1, ..., c + p - 1.
public export
countFrom : (p : Nat) -> (c : Nat) -> Vect p Nat
countFrom 0 c = []
countFrom (S p) c = c :: countFrom p (S c)

||| The second component of an LFstPair.
public export
sndLFP : LFstPair a b -> b
sndLFP ((#) _ b) = b

||| newQubitsPointers p c hands out the identifiers countFrom p c and returns the counter p + c.
export
newQubitsPointersIds : {n : Nat} -> (p : Nat) -> (c : Nat) -> (xs : Vect n Qubit)
                    -> (toVectN (fst (sndLFP (newQubitsPointers p c xs))) = countFrom p c,
                        snd (sndLFP (newQubitsPointers p c xs)) = p + c)
newQubitsPointersIds 0 c xs = (Refl, Refl)
newQubitsPointersIds (S p) c xs with (newQubitsPointersIds p (S c) (MkQubit c :: xs))
  newQubitsPointersIds (S p) c xs | (ih1, ih2) with (newQubitsPointers p (S c) (MkQubit c :: xs))
    newQubitsPointersIds (S p) c xs | (ih1, ih2) | (q # (v, nc)) =
      (cong (c ::) ih1, rewrite plusSuccRightSucc p c in ih2)

leSelfVoid : LTE (S x) x -> Void
leSelfVoid (LTESucc l) = leSelfVoid l

leRefl : (c : Nat) -> LTE c c
leRefl 0 = LTEZero
leRefl (S k) = LTESucc (leRefl k)

leAddLeft : (p, c : Nat) -> LTE c (p + c)
leAddLeft p c = rewrite plusCommutative p c in lteAddRight c

allAtLeastWeaken : All (\k => LTE (S c) k) ks -> All (\k => LTE c k) ks
allAtLeastWeaken [] = []
allAtLeastWeaken (l :: ls) = lteSuccLeft l :: allAtLeastWeaken ls

||| Every identifier in countFrom p c is at least c.
countFromAtLeast : (p, c : Nat) -> All (\k => LTE c k) (countFrom p c)
countFromAtLeast 0 c = []
countFromAtLeast (S p) c = leRefl c :: allAtLeastWeaken (countFromAtLeast p (S c))

||| Every identifier in countFrom p c is below p + c.
countFromBelow : (p, c : Nat) -> Below (p + c) (countFrom p c)
countFromBelow 0 c = []
countFromBelow (S p) c =
  LTESucc (leAddLeft p c) :: (rewrite plusSuccRightSucc p c in countFromBelow p (S c))

||| x differs from every identifier that is bigger than x.
diffFromBigger : {0 x : Nat} -> {0 ks : Vect n Nat} -> All (\k => LTE (S x) k) ks -> IsDifferentDec x ks
diffFromBigger {ks = []} [] = IsDiffNilDec
diffFromBigger {ks = k :: _} (l :: ls) =
  IsDiffSuccDec (\eq => leSelfVoid (replace {p = \y => LTE (S y) k} eq l)) (diffFromBigger ls)

||| The identifiers countFrom p c are pairwise different.
countFromDiff : (p, c : Nat) -> AllDifferentDec (countFrom p c)
countFromDiff 0 c = AllDiffNilDec
countFromDiff (S p) c = AllDiffSuccDec (diffFromBigger (countFromAtLeast p (S c))) (countFromDiff p (S c))

toVectNAppend : (v : Vect n Qubit) -> (w : Vect m Qubit) -> toVectN (v ++ w) = toVectN v ++ toVectN w
toVectNAppend [] w = Refl
toVectNAppend (MkQubit k :: v) w = cong (k ::) (toVectNAppend v w)

diffAppend : IsDifferentDec x xs -> IsDifferentDec x ys -> IsDifferentDec x (xs ++ ys)
diffAppend IsDiffNilDec dy = dy
diffAppend (IsDiffSuccDec ne dx) dy = IsDiffSuccDec ne (diffAppend dx dy)

||| An identifier below c differs from every identifier that is at least c.
belowDiff : {0 x : Nat} -> {0 ks : Vect n Nat} -> LT x c -> All (\k => LTE c k) ks -> IsDifferentDec x ks
belowDiff {ks = []} lt [] = IsDiffNilDec
belowDiff {ks = k :: _} lt (l :: ls) =
  IsDiffSuccDec (\eq => leSelfVoid (replace {p = \y => LTE (S y) k} eq (lteTransitive lt l))) (belowDiff lt ls)

allDiffAppend : AllDifferentDec xs -> AllDifferentDec ys -> Below c xs -> All (\k => LTE c k) ys
             -> AllDifferentDec (xs ++ ys)
allDiffAppend AllDiffNilDec dys [] ge = dys
allDiffAppend (AllDiffSuccDec dx dxs) dys (b :: bs) ge =
  AllDiffSuccDec (diffAppend dx (belowDiff b ge)) (allDiffAppend dxs dys bs ge)

belowAppend : Below c xs -> Below c ys -> Below c (xs ++ ys)
belowAppend [] bys = bys
belowAppend (b :: bs) bys = b :: belowAppend bs bys

belowWeaken : LTE c d -> Below c xs -> Below d xs
belowWeaken le [] = []
belowWeaken le (b :: bs) = lteTransitive b le :: belowWeaken le bs

||| newQubits keeps the invariant: the new identifiers are counter, ..., counter + p - 1, none of
||| them live and all different, and the counter moves past them.
export
newQubitsFresh : {n : Nat} -> (p : Nat) -> (c : Nat) -> (v : Vect n Qubit) -> FreshIds v c
              -> FreshIds (v ++ fst (sndLFP (newQubitsPointers p c v))) (snd (sndLFP (newQubitsPointers p c v)))
newQubitsFresh p c v (dv, bv) with (newQubitsPointersIds p c v)
  newQubitsFresh p c v (dv, bv) | (ids, cnt) =
    rewrite cnt in rewrite toVectNAppend v (fst (sndLFP (newQubitsPointers p c v))) in rewrite ids in
      (allDiffAppend dv (countFromDiff p c) bv (countFromAtLeast p c),
       belowAppend (belowWeaken (leAddLeft p c) bv) (countFromBelow p c))

||| Removing a handle keeps every property that all live identifiers have.
removeElemAll' : {0 pr : Nat -> Type} -> {n : Nat} -> (k : Nat) -> (xs : Vect n Qubit) -> (i : Nat)
              -> All pr (toVectN (MkQubit k :: xs)) -> All pr (toVectN (removeElem (MkQubit k :: xs) i))
removeElemAll' k xs 0 (a :: as) = as
removeElemAll' k [] (S i) _ = []
removeElemAll' k (MkQubit j :: ys) (S i) (a :: as) = a :: removeElemAll' j ys i as

removeElemAll : {0 pr : Nat -> Type} -> {n : Nat} -> (w : Vect (S n) Qubit) -> (i : Nat)
             -> All pr (toVectN w) -> All pr (toVectN (removeElem w i))
removeElemAll (MkQubit k :: xs) i as = removeElemAll' k xs i as

diffToAll : IsDifferentDec x ks -> All (\k => x = k -> Void) ks
diffToAll IsDiffNilDec = []
diffToAll (IsDiffSuccDec ne d) = ne :: diffToAll d

allToDiff : All (\k => x = k -> Void) ks -> IsDifferentDec x ks
allToDiff [] = IsDiffNilDec
allToDiff (ne :: as) = IsDiffSuccDec ne (allToDiff as)

||| Removing a handle keeps the live identifiers pairwise different.
allDiffRemove' : {n : Nat} -> (k : Nat) -> (xs : Vect n Qubit) -> (i : Nat)
              -> AllDifferentDec (toVectN (MkQubit k :: xs))
              -> AllDifferentDec (toVectN (removeElem (MkQubit k :: xs) i))
allDiffRemove' k xs 0 (AllDiffSuccDec _ d) = d
allDiffRemove' k [] (S i) _ = AllDiffNilDec
allDiffRemove' k (MkQubit j :: ys) (S i) (AllDiffSuccDec dk d) =
  AllDiffSuccDec (allToDiff (removeElemAll' j ys i (diffToAll dk))) (allDiffRemove' j ys i d)

allDiffRemove : {n : Nat} -> (w : Vect (S n) Qubit) -> (i : Nat)
             -> AllDifferentDec (toVectN w) -> AllDifferentDec (toVectN (removeElem w i))
allDiffRemove (MkQubit k :: xs) i d = allDiffRemove' k xs i d

||| measure keeps the invariant: it removes the measured handle and keeps the counter.
export
measureFresh : {n : Nat} -> (w : Vect (S n) Qubit) -> (i : Nat) -> (c : Nat) -> FreshIds w c
            -> FreshIds (removeElem w i) c
measureFresh w i c (d, b) = (allDiffRemove w i d, removeElemAll w i b)

||| The identifier invariant of a SimulatedOp state.
public export
Fresh : SimulatedOp n -> Type
Fresh (MkSimulatedOp _ _ v c) = FreshIds v c

||| applyCirc changes only the amplitudes, so it keeps Fresh. It finishes applyUST and applyUnitaryDirectly.
export
applyCircFresh : {n : Nat} -> (ks : Vect n Nat) -> (u : Unitary n) -> (s : SimulatedOp n) -> Fresh s
              -> Fresh (applyCirc ks u s)
applyCircFresh ks IdGate s fr = fr
applyCircFresh ks (H j g) s fr with (applyCircFresh ks g s fr)
  _ | ih with (applyCirc ks g s)
    _ | (MkSimulatedOp _ _ _ _) = ih
applyCircFresh ks (P p j g) s fr with (applyCircFresh ks g s fr)
  _ | ih with (applyCirc ks g s)
    _ | (MkSimulatedOp _ _ _ _) = ih
applyCircFresh ks (CNOT c t g) s fr with (applyCircFresh ks g s fr)
  _ | ih with (applyCirc ks g s)
    _ | (MkSimulatedOp _ _ _ _) = ih
