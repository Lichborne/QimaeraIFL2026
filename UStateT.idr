module UStateT
import Control.Monad.State
import LinearTypes
import UnitaryLinear




||| The UStateT monad is a linear state monad, similar to QStateT but without the IO monad. 
|||It is used for linear computations that do not involve IO, such as unitary operations on quantum states. 
export
data UStateT : (initialType : Type) -> (finalType : Type) -> (returnType : Type) -> Type where
  MkUST : (1 _ : (1 _ : initialType) -> (LPair finalType returnType)) -> UStateT initialType finalType returnType

||| Unwrap and apply a UStateT monad computation.
public export
runUStateT : (1 _ : initialType) -> (1 _ : UStateT initialType finalType returnType) -> (LPair finalType returnType)
runUStateT i (MkUST f) = f i

||| The exported way to build a UStateT computation. This is to avoid pattern matching on the constructor.
public export
mkUST : (1 _ : (1 _ : initialType) -> (LPair finalType returnType)) -> UStateT initialType finalType returnType
mkUST f = MkUST f

public export
pure : (1 _ : a) -> UStateT t t a
pure x = MkUST (\st => (st # x))

public export
(>>=) : (1 _ : UStateT i m a) -> (1 _ : ((1 _ : a) -> UStateT m o b)) -> UStateT i o b
v >>= f =  MkUST  $ \i => let (a # m) = runUStateT i v in runUStateT a (f m)

public export
modify : ((1 _ : i) -> o) -> UStateT i o ()
modify f = MkUST $ \i => (f i # ())

