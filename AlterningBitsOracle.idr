module AlterningBitsOracle

import Data.Nat
import UnitaryLinear
import Lemmas
import NatRules


%default total

|||Alternating bits oracle : checks if the input alternates, i-e does not have a pair of adjacent qubits in stae 00 or 11


lemmaFlip : (i : Nat) -> (k : Nat) -> (p : LT (S (S i)) k) -> LT i k
lemmaFlip 0 k p = lemmaCompLT0 k 2 
lemmaFlip (S i) (S k) p = lemmaLTSuccLT (S i) (S k) (lemmaLTSuccLT (S (S i)) (S k) p)

lemmaSolve : (n : Nat) -> LT n (S (S n))
lemmaSolve any = lemmaLTESuccLTE (S any) (S (S any)) (lemmaLTSucc (S any))

flip : (n : Nat) -> (i : Nat) -> {auto prf : LT i (S (S n))} -> Unitary (S (S n))
flip n 0 = X 0 IdGate
flip n 1 = X 1 IdGate
flip n (S (S i)) = X (S (S i)) (flip n i {prf = lemmaFlip i (S (S n)) prf})


export 
solve : (n : Nat) -> Unitary ((S (S n)) + 1)
solve n = 
  let circ1 = tensor (flip n (S n)) (IdGate {n=1})
      circ2 = tensor (flip n n) (IdGate {n = 1})
      circ1' = circ1 . generalizedToffoli ((S (S n)) + 1) . circ1
      circ2' = circ2 . generalizedToffoli ((S (S n)) + 1) . circ2
  in circ1' . circ2'
