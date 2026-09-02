module Main

import Data.Nat
import Data.Vect
import Data.List
import LinearTypes
import Control.Linear.LIO
import Lemmas
import UnitaryLinear
import QStateT
import UStateT
import UnitarySim
import System.Random
import Injection
import QFT
import Grover
import VQE
import Complex
import CoinToss
import QAOA
import Graph
import Examples
import RUS
import Matrix
import UnitarySim
import ModularExponentiation
import BinarySimulatedOp
import SimulatedOp
import QuantumOp
import UnitaryNoPrf
--import UnitaryNoPrfSim


-- %default total
  

||| Perform 1000 fair coin tosses and count the number of heads
||| (via simulating the quantum dynamics).
testCoins : IO ()
testCoins = do
  let f = coin {t = SimulatedOp}
  s <- sequence (Data.List.replicate 1000 f)
  putStrLn $ "Number of heads: " ++ (show (length (filter (== True) s)))


||| Test graph for the QAOA problem
export
graph1 : Graph 5
graph1 = AddVertex (AddVertex (AddVertex (AddVertex (AddVertex Empty []) [True]) [True, True]) [False, True, False]) [False, False, True, True]

||| Execute QAOA with 100 samples on the previous graph to solve the MAXCUT problem
export
testQAOA : IO (Cut 5)
testQAOA = do
  QAOA {t = SimulatedOp} 100 1 graph1


||| Small test for the VQE algorithm
export
testVQE : IO Double
testVQE = do
  putStrLn "Test VQE"
  let hamiltonian = [(2, [PauliX, PauliY]),(3,[PauliZ, PauliI])]
  VQE {t = SimulatedOp} 2 hamiltonian 5 10 5

||| a few tests for QFT
export
qftTestIo : IO ()
qftTestIo = let
  un3 = qftInUnitary {n = 3}
  unBasicU = qftUTest -- basic test of qft with unitary application inside
  unBasic = qftTest -- basic test of fully monadic qft
  unUShuffle = qftUTest_Shuffle_3120 -- qubits are scrambled on purpose for testing purposes, see examples.idr
  unShuffle = qftTest_Shuffle_3120 -- as above
  unCtrl = qftControlTest --  as above
  in
    do
      () <- putStrLn "Testing building of QFT over 3 qubits, Output in qft3.py"
      d <- draw un3
      eo <- exportToQiskit "qft3.py" un3
      () <- putStrLn "Testing building of QFT over 4 qubits with UnitaryRun, with shuffled qubits. Output in qftUTest.py"
      d <- draw unBasicU
      eo <- exportToQiskit "qftUTest.py" unBasicU
      () <- putStrLn "Testing building of QFT(abstract implementation) over 4 qubits with UnitaryRun. Output in qftTest.py"
      d <- draw unBasic
      eo <- exportToQiskit "qftTest.py" unBasic
      () <- putStrLn "Testing building of QFT over 4 qubits with UnitaryRun, with shuffled qubits. Output in qftUTest.py"
      d <- draw unUShuffle
      eo <- exportToQiskit "qftUTestShuffle.py" unUShuffle
      () <- putStrLn "Testing building of QFT(abstract implementation) over 4 qubits with UnitaryRun. Output in qftTest.py"
      d <- draw unShuffle
      eo <- exportToQiskit "qftTestShuffle.py" unShuffle
      () <- putStrLn "Testing building of controlled QFT(abstract implementation) over 4 qubits (3 plus control) with UnitaryRun. Output in qftControlTest.py"
      d <- draw unCtrl
      eo <- exportToQiskit "qftControlTest.py" unCtrl
      pure ()  

||| two tests for the modular adder, using different implementations
export
adderTestIo : IO ()
adderTestIo = let (uni) = adderTest in
    do
      () <- putStrLn "Testing building  unitary adder (3 + 4 qubits). Output in adderTest.py"
      d2 <- draw uni
      eo <- exportToQiskit "adderTest.py" uni
      () <- putStrLn "Testing building  unitary adder (3 + 4 qubits). For the second example, run with BinarySimulatedOp, you will have to provide and output file name without extension."
      uniq <- adderTestQ
      pure ()
      

||| Test for Modular Exponentiation (unitary contruction). Takes long, so call will remain commented out by default
export
modularTestIo : IO (Unitary 33)
modularTestIo = let
  (uni) = modularTest
  in
    do
      () <- putStrLn "Testing modular exponentiation for a small input. Output in modularTest.py"
      d <- draw uni
      eo <- exportToQiskit "modularTest.py" uni
      pure uni

||| abstract control test using UnitaryNoPrf and Unitary to compare
export
absControlTestIo : IO ((Unitary 5))
absControlTestIo = let
  --(uniNoPrf) = absControlTestNoPrf
  (uni) = absControlTest
  in
    do
      --() <- putStrLn "Testing triply abstract-controlled CNot on last 2 indeces with UnitaryNoPrf. Output in absControlTest.py"
      --d1 <- draw uniNoPrf
      () <- putStrLn "Testing triply abstract-controlled CNot on last 2 indeces with Unitary. Output in absControlTestNoPrf.py"
      d2 <- draw uni
      --eo <- exportToQiskit "absControlTest.py" uniNoPrf
      eo <- exportToQiskit "absControlTest.py" uni
      cccn <- draw cccnot 
      eo <- exportToQiskit "absControlRef.py" cccnot
      pure ( uni)


partial public export
main : IO ()
main = do

  -- Execute the example file and draw the circuit examples
  drawExamples

  -- Execute the coin toss example
  putStrLn "\nTest coin toss by performing 1000 coin tosses."
  testCoins

  -- Repeat until success
  putStrLn "\nTest 'Repeat Until Success'. Probability to measure '1' is 2/3 for this example."
  putStrLn "\nYou will have to provide a name for each output file, as these are three separate runs, each until success."
  b <- testMultipleRUS 3

  -- VQE
  putStrLn "\nSmall test with VQE"
  --
  r <- testVQE
  putStrLn $ "result from VQE : " ++ show r

  -- QAOA 
  putStrLn "\nSmall test with Encoding in VQE"
  cut <- testQAOA
  putStrLn $ "result from QAOA : " ++ show cut

  --Modular exponentiation - commented because it takes a while.
  --modular <- modularTestIo

  --Some QFT tests
  qftUTest <- qftTestIo

  --Tests of abstract control
  absControl <- absControlTestIo

  --inplace adder tests
  adder <- adderTestIo
  pure ()





