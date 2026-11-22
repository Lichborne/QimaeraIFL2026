||| Root module of the library core.
|||
||| Idris scopes `private` names by namespace: a module can see the private names of
||| every module above it in the namespace hierarchy. So every Qimaera.Core.* module (the
||| two monads, the interfaces in Qimaera.Core.QuantumOp and the concrete implementations
||| in Qimaera.Core.Implementations.*) can use the private definitions below, while code
||| outside the Qimaera.Core namespace cannot construct, take apart or run a UStateT or
||| QStateT computation itself: it can only compose the interfaces' operations.
module Qimaera.Core

import Data.Nat
import Data.Vect
import Utilities.LinearTypes
import Utilities.UnitaryLinear
import Utilities.Complex
import Utilities.Matrix
import Control.Linear.LIO

%default total

||| Linear IO, the monad underneath QStateT.
public export
R : Type -> Type
R = L IO {use = Linear}

||| The UStateT monad is a linear state monad, similar to QStateT but without the IO monad.
||| It is used for linear computations that do not involve IO, such as unitary operations on quantum states.
||| The type is exported; its constructor is private to the Qimaera namespace.
export
data UStateT : (initialType : Type) -> (finalType : Type) -> (returnType : Type) -> Type where
  MkUST : (1 _ : (1 _ : initialType) -> (LPair finalType returnType)) -> UStateT initialType finalType returnType

||| The QStateT monad: a linear state monad over linear IO (inspired by the indexed state monad in Haskell).
||| The type is exported; its constructor is private to the Qimaera namespace.
export
data QStateT : (initialType : Type) -> (finalType : Type) -> (returnType : Type) -> Type where
  MkQST : (1 _ : (1 _ : initialType) -> R (LPair finalType returnType)) -> QStateT initialType finalType returnType

||| State of the linear-algebraic simulator: amplitudes, the unitary built so far, the qubit
||| handles in position order and a counter. It holds qubit handles, so its constructor must
||| not reach client code. It is generic in the handle type so that it can be defined here,
||| above both Qimaera.Core.QuantumOp (where Qubit and its private constructor live) and the
||| implementations; Qimaera.Core.QuantumOp defines SimulatedOp = SimulatedOpOf Qubit.
export
data SimulatedOpOf : (qubit : Type) -> Nat -> Type where
  MkSimulatedOp : {n : Nat} -> Matrix (power 2 n) 1 -> Unitary n -> Vect n qubit -> Nat -> SimulatedOpOf qubit n

||| State of the circuit-exporting simulator; same visibility as SimulatedOpOf.
||| The counter (Nat) here is a count for how many functions we have.
export
data BinarySimulatedOpOf : (qubit : Type) -> Nat -> Type where
  MkBinarySimulatedOp : {n : Nat} -> Unitary n -> Vect n qubit -> Nat -> String -> BinarySimulatedOpOf qubit n

||| Build a UStateT computation from a state transformer (for the library's modules).
private
mkUST : (1 _ : (1 _ : initialType) -> (LPair finalType returnType)) -> UStateT initialType finalType returnType
mkUST f = MkUST f

||| Unwrap and apply a UStateT computation to a state (for the library's modules).
private
runUStateT : (1 _ : initialType) -> (1 _ : UStateT initialType finalType returnType) -> (LPair finalType returnType)
runUStateT i (MkUST f) = f i

||| Unwrap and apply a QStateT computation to a state (for the library's modules).
private
runQStateT : (1 _ : initialType) -> (1 _ : QStateT initialType finalType returnType) -> R (LPair finalType returnType)
runQStateT i (MkQST f) = f i
