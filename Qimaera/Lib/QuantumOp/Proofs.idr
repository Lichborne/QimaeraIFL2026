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

private
lids : LVect n Qubit -> Vect n Nat
lids [] = []
lids (q :: qs) = qid q :: lids qs

||| The handle utilities give back the handles they are given, with their ids.
private
qubitToNatPairIs : (q : Qubit) -> qubitToNatPair q = (q # qid q)
qubitToNatPairIs (MkQubit k) = Refl

private
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