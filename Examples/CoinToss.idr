module Examples.CoinToss

import Data.Vect
import Qimaera.Lib.QStateT
import Qimaera.Lib.QuantumOp
import Utilities.LinearTypes
import Qimaera.Lib.ConcreteImplementations.SimulatedOp
import Utilities.Lemmas

||| A fair coin toss (as an IO effect) via quantum resources.
|||
||| first create a new qubit in state |0>
||| then apply a hadamard gate to it, thereby preparing state |+>
||| and finally measure the qubit and return this as the result
export
coin : UnitaryOp t => QuantumOp t => IO Bool
coin = do
  [b] <- run {t = t} (do
           q <- newQubit
           q <- applyUST (applyH q)
           r <- measure q
           pure r
         )
  pure b

testCoin : IO Bool
testCoin = coin {t = SimulatedOp}
