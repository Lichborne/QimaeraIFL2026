||| Exports the controlled multiplication x -> a x mod N built by modularN 4 a N (11 qubits),
||| for every N < 16 and every a coprime to N, as Qiskit files qme_N_a.py in the current
||| directory. Examples/check_qme.py simulates them and checks the result (see README).
module Examples.QMESweep

import Data.Nat
import Utilities.UnitaryLinear
import Algorithms.ModularExponentiation

||| a is coprime to n exactly when some k < n has a * k = 1 mod n.
coprime : Nat -> Nat -> Bool
coprime n a = any (\k => (a * k) `mod` n == 1) [1 .. minus n 1]

main : IO ()
main = for_ [2 .. 15] $ \bigN =>
  for_ [1 .. minus bigN 1] $ \a =>
    when (coprime bigN a) $
      exportToQiskit ("qme_" ++ show bigN ++ "_" ++ show a ++ ".py") (modularN 4 a bigN)
