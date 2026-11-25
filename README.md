# Qimaera
Idris libraries for hybrid classical-quantum programming.

## <a id="installing"></a> Installing Idris2

The current version of the library works for Idris2 0.7.0.

The latest version of Idris can be found [here](https://www.idris-lang.org/pages/download.html), and all the instructions for installing it can be found [here](https://idris2.readthedocs.io/en/latest/tutorial/starting.html).

## <a id="compiling"></a> Compiling Qimaera

Type `make` to compile the main file and `./build/exec/main` to run it.

Compiling individual files can be done from the repository root with `idris2 -p contrib -p linear "path/to/filename.idr"`, for example `idris2 -p contrib -p linear Algorithms/QFT.idr` (module names follow the folders, so Idris must be started from the root).

When compiling individual files, there may be compiler warnings due to the infix notation used.

If wishing to run individual test cases (with IO outputs), the `:exec` Idris2 command should be used once a file is loaded. If such functions are called directly, the process will take a very long time, as the expression is then elaborated by the interpreter purely symbolically.

## <a id="getting_started"></a> Getting Started

We strongly recommend starting by reading the following paper: https://arxiv.org/abs/2111.10867. It describes some of the main design ideas and explains how some of our libraries and functions should be understood.

However, note that this is an update to the original, with no publicly available paper yet. We recommend reading and executing the code from file `Examples/Examples.idr`. It contains simple examples using the functions defined in `Utilities/UnitaryLinear.idr` and `Qimaera/Lib/QuantumOp.idr`.

## <a id="layout"></a> Repository Layout

* `Main.idr`: the main file, built by `make`.
* `Qimaera/Lib.idr` and `Qimaera/Lib/`: the library. `Qimaera/Lib.idr` is its root module: the types of the `UStateT` and `QStateT` monads, the private functions that run them, and the simulator states. `Qimaera/Lib/` holds the monads and the `UnitaryOp`, `QuantumOp` and `RunUnitaryOp` interfaces (in `Qimaera/Lib/QuantumOp.idr`).
* `Qimaera/Lib/ConcreteImplementations/`: the concrete implementations of the interfaces.
* `Utilities/`: background modules the library builds on (linear types, lemmas, matrices, complex numbers, the `Unitary` datatypes and so on).
* `Algorithms/`: quantum algorithms written with the library (QFT, Grover, QAOA, VQE, repeat-until-success, modular exponentiation).
* `Examples/`: smaller examples, including the detectable-error examples.

Idris scopes private names by namespace: a module can see the private names of the modules above it in the namespace hierarchy. The functions that run `UStateT` and `QStateT` computations are private in `Qimaera/Lib.idr`, so the interfaces and the implementations, which all live under `Qimaera.Lib`, can run computations, while code outside that namespace can only compose the operations of the interfaces. The simulator states are defined there too, with private constructors, so that both `Qimaera/Lib/QuantumOp.idr` and the simulators can open them but client code cannot. The qubit constructor `MkQubit` is private in `Qimaera/Lib/QuantumOp.idr`, so none of the implementations in `Qimaera/Lib/ConcreteImplementations/`, including the simulators' `UnitaryOp` code, can see it.

## <a id="overview"></a> Library Overview

### **`Utilities/UnitaryLinear.idr`**

An algebraic representation of unitary quantum circuits that is linear in its arguments due to this being a condition for use
in the bastract interface.

The `Unitary` data type represents unitary circuits.
The `Unitary` data type is parametrized by the arity of the corresponding unitary operator. It has 4 constructors : 

 * `IdGate` : parametrized by a natural number n, it represents a circuit with n wires, without any other gate applied to any of the wires.
 * `H`      : Hadamard gate, takes as argument the index of the wire on which it should be applied (for a circuit of size n, the indices go from 0 to n-1). The second argument, which is implicit (and can be often inferred by the compiler), is a proof obligation that this index is smaller than the size of the circuit.
 * `P`      : Phase gate, its first argument (a Double) being the associated phase. The other arguments serve the same purpose as H.
 * `CNOT`   : Controlled-NOT gate to the control (c argument) and the target (t argument) wires. Here, we add the constraint that the two wires have to be distinct.
 
As all quantum circuits can be represented as a composition or tensor product of Hadamard, Phase and CNOT gates, we only need these three constructors to build any circuit.


Higher level functions to build more complicated circuits are also defined in this file :

 * `compose`    : sequential composition of unitary circuits.
 * `tensor`     : parallel composition (tensor product) of unitary circuits.
 * `apply`      : apply some unitary circuit to another one.
 * `adjoint`    : the adjoint of a unitary circuit.
 * `controlled` : controlled version of a unitary circuit.

Some examples using these functions can be found in the `Examples/Examples.idr` file.

The most common gates (HGate, PGate, CNOTGate, TGate, SGate, ZGate, XGate, RxGate, RyGate, RzGate) are given as unitary gates of size 1 or 2.

Visualize circuits : 

 * `draw`           : Draw a circuit in the terminal.
 * `exportToQiskit` : Export a circuit to Qiskit code for a graphical rendering.

There are also other ways of formatting with different styles of output in mind.
This file also provides some function to compute the number of gates and the depth of a circuit.



### **`Qimaera/Lib/QStateT.idr`**

Quantum state transformer for effectful quantum computation (used in the file `Qimaera/Lib/QuantumOp.idr`).

The type `QStateT initialType finalType returnType` means we are performing a quantum operation from an initial state with type initialType, to a final state with type finalType, and we return a user-accessible value of type returnType.

This was inspired by the indexed state monad in Haskell and we adapted it to also handle linearity, probabilistic effects and IO effects. 


### **`Qimaera/Lib/QuantumOp.idr`**

Defines the `Qubit` type, the `QuantumOp` and `UnitaryOp` interfaces for quantum operations and building unitaries and provides part of an implementation with linear algebraic simulation for both. This file is long due to access control requirements on Qubits.

The Qubit type is used to identify individual qubits. This type does not carry any quantum state information.

The QuantumOp interface is an abstraction used to represent quantum operations. It introduces a few operations on qubits:

 * `newQubits`    : Adds p new qubits to a quantum state.
 * `applyUST`: Lift a UStateT up from UnitaryOp and apply it according to the qubits passed down to it in QuantumOp
 * `applyUnitaryDirectly` : Apply a unitary circuit to a selection of qubits. The parameters are the linear vector of qubit identifiers for the set of qubits and the unitary operator.
 * `measure`      : Measure a set of qubits.
 * `run`          : Execute a sequence of quantum operations.

The UnitaryOp interface uses information about available qubits provided to it by QuantumOp (or UnitaryRun, see below) to construct unitaries correctly but avoiding proof obligations. It can be used abstractly or utilizing the Unitary datatype (see Algorithms/QFT.idr for examples, for instance). Its functions are described in detail in the file.

Further, the `UnitaryRun` interface, which can be used to obtain an instance of the Unitary datatype out of UnitaryOp by simply supplying Qubits to it is also found in this file. Its use is straighforward based on QuantumOp and accompanying examples.

We also provide a concrete implementation of these interfaces. In this file, SimulatedOp provides linear-algebraic simulation of all the required quantum operations for QuantumOp. SimulatedOp's implementation of UnitaryOp is found in `Qimaera/Lib/ConcreteImplementations/SimulatedOp.idr`

### **`Qimaera/Lib/QuantumOp/Proofs.idr`**

Proofs about qubit identifiers and wires (Section 4.3 of the paper). The identifier invariant `FreshIds` (the identifiers of live qubits are pairwise different and below the allocation counter) holds at the start (`freshStart`) and is kept by allocation (`newQubitsFresh`), measurement (`measureFresh`) and applying a unitary (`applyCircFresh`). For live handles with pairwise different identifiers, `positions` gives distinct wires in range (`positionsInjective`), so the run-time check passes (`checkPasses`) and `applySafe` is `apply` (`applySafeIsApply`). It is `%default total`.

### **`Qimaera/Lib/ConcreteImplementations/SimulatedOp.idr`**

Implements UnitaryOp using SimulatedOp. Unitary is used to collect the unitary bits, but linear algebra would work too (although it is very slow) for. both states and unitaries. Note that the counter has, in the new implementation, become vacuous, and therefore can be repurposed or removed.

### **`Qimaera/Lib/ConcreteImplementations/SimulatedOp/Proofs.idr`**

Proofs about SimulatedOp's implementation of UnitaryOp (Section 4.3 of the paper). Each operation reduces to `applySafe` at the positions of its handles (the `...Runs` lemmas; `applyUnitaryApplies` combines this with `checkPasses` and `applySafeIsApply`) and keeps the live handles and the counter (`KeepsFrame` and the `...Keeps` lemmas), so it keeps `FreshIds` (`keepsFresh`). It is `%default total`.

### **`Qimaera/Lib/ConcreteImplementations/BinarySimulatedOp.idr`**

Implements UnitaryOp using BinarySimulatedOp, i.e. binary simulation of the quantum state. When an algorithm is run using this, the circuit, in cluding measurements, created is exported to a file with a name of the user's choosing. The implementation is split into (numbered) functions automatically, as well, for future visualization purposes. File outputs require Matplotlib package to run (last line of code, can be removed).

### **`Examples/Examples.idr`**

This file contains simple examples of programs (unitary circuits and quantum operations) to get started with the libraries.

### **`Examples/ExampleDetectableErrors.idr`**

This file contains common examples of inadmissible programs that can be detected by the Idris type checker.


### **`Utilities/Lemmas.idr`**

Proofs of all the lemmas used to define all the basic function in `Unitary.idr`. Some of these lemmas are reused in quantum algorithms.

### **`Utilities/LinearTypes.idr`**

Defines some linear types such as linear vectors, and implements some basic functions with these types.

### **`Utilities/Matrix.idr`**

Defines all necesary matrix operations for the linear-algebraic simulation.

### **`Algorithms/QFT.idr`**

The quantum circuit for the Quantum Fourier Transform. Calling `qft n` returns the QFT on n qubits.

### **`Teleportation.idr`**

Implementation of the quantum teleportation protocol. 

### **`Algorithms/QAOA.idr`**

Implementation of QAOA with the vanilla optimisation procedure to solve the MAXCUT problem.
QAOA is an example of a variational quantum algorithm that is used to solve optimisation problems.
This code shows how classical and quantum programming interact with each other.


### **`Algorithms/Graph.idr`**

Definition of graphs used in `Algorithms/QAOA.idr` for solving the MAXCUT problem.

### **`Algorithms/VQE.idr`**

Implementation of the VQE algorithm with a vanilla classical optimisation strategy.
It is also a variational quantum algorithm.

### **`Algorithms/RUS.idr`**

Implementation of the Repeat Until Success algorithm.

This example illustrates the difference between computing unitary operators and doing effectful quantum operations: here we realise a quantum unitary operator by using measurements and recursion.

Given an input qubit |q> and a single-qubit unitary operation U, return the state U|q>. The "Repeat Until Success" approach solves this problem in the following way:

 1. Prepare a new qubit in state |0>.
 2. Apply a two-qubit unitary operator U' (chosen in advance depending on U).
 3. Measure the first qubit.
 4. If the measurement outcome is 0, then the output state is U |psi>, as required, and the algorithm terminates; otherwise the current state is E|psi>, where E is some other unitary operator (chosen in advance depending on U), so we apply $E^\dagger$ to
this state and we go back to step (1).

### **`Examples/CoinToss.idr`**

A quantum state transformer which realises a fair coin toss in the obvious way: 

 * first create a new qubit in state |0>
 * then apply a hadamard gate to it, thereby preparing state |+>
 * and finally measure the qubit and return this as the result


### **`Utilities/OptimiseUnitary.idr`**

A simple function for basic optimisation of quantum circuits. The main purpose here is to show how unitary circuits in Qimaera can be manipulated to be optimised with respect to some criterion.

### **`Qimaera/Lib/ConcreteImplementations/UnitarySim.idr`**

An implementation of UnitaryOp using the linear Unitary datatype.

### **`Utilities/UnitaryNoPrf.idr`**

Unitary datatype without the proofs required for correctness. Useful for development, and for seeing that the abstract strucute enforces correctness without the explicit proofs. This can be seen via the implementation in Qimaera/Lib/ConcreteImplementations/UnitaryNoPrfSim.idr

### **`Qimaera/Lib/ConcreteImplementations/UnitaryNoPrfSim.idr`**

Implements UnitaryOp using UnitaryNoPrf. 

### **`Qimaera/Lib/UStateT.idr`**

Unitary state transformer for effectful quantum computation. Similar to QStateT, except IO is not linear.

### **`Qimaera/Lib/UStateT/Proofs.idr`**

Proofs about UStateT that hold for any implementation: whatever each operation preserves, every UnitaryOp program preserves (`bindKeeps`). It is `%default total`.

### **`QubitDevelopment.idr`**

This file contains Unique Linear Vectors and other Qubit related developments, and is separate from the main files

### **`Algorithms/ModularExponentiation.idr`**

Implementation of Quantum Modular Exponentiation. This is done using a paradigm where some ofthe Qubits are carried in separate linear vectors in order to keep track of them more easily. Some of the implementation is given using the usual paradigm used to define other functions on order to check that this new approach parses correctly.

### **`Examples/QMESweep.idr`**

Exports the controlled multiplication `modularN 4 a N` (11 qubits) for every N < 16 and every a coprime to N, 71 circuits in all, as Qiskit files `qme_N_a.py` in the current directory. Build it with `idris2 -p contrib -p linear Examples/QMESweep.idr -o qmesweep` and run it in an empty directory, e.g. `mkdir qme && cd qme && ../build/exec/qmesweep`.

### **`Examples/check_qme.py`**

Simulates the circuits written by `Examples/QMESweep.idr` on every valid classical input (control qubit 0 or 1, x < N, other registers 0) and checks that each gives a x mod N when the control is set and leaves x unchanged otherwise. Run `python3 ../Examples/check_qme.py` in the directory with the circuits. Requires NumPy.

### **`Utilities/NatRules.idr`**

Some rules for natural numbers that Idris does not see from Data.Nat for one reason or another. These are taken directly from Idris 2's github repository, for the most part.

### **`Utilities/QuditMatrix.idr`**

Base (in)dependent Unitary matrix library. Can be used for generalizing concrete circuits to qudits. Qudit wires are numbered as qubit wires are: wire 0 is the most significant digit of a basis index (the first tensor factor), so with base 2 the qudit matrices are the qubit ones.

### **`Qimaera/Lib/ConcreteImplementations/QuditMatrixSim.idr`**

UnitaryOp implementations dependent on the chosen "base" for qudit matrices. For a given choice of quantum data, a particular concrete implementation involves simply concretizing "base" in the functions provided

### **`Main.idr`**

More examples of the different algorithms we implemented.
Uncomment some lines to execute the corresponding programs.

### **`Examples/LinearCommandBufferExample.hs`**

Haskell implementation of the structure used for UnitaryOp for a different, classical example: Linear Command Buffers. 
