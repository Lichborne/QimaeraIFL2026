module ErrorExamples
import Data.Linear.LVect
import Data.Linear.Notation

||| Firstly, we have a linear state transformer monad as below, with the usual functions. In actuality, two slightly
||| different versions of this are used in the abstract interfaces, but this is sufficient to produce the bug.
public export
data LStateT: (initialType : Type) -> (finalType : Type) -> (returnType : Type) -> Type where
  MkLST : (initialType -@ (LPair finalType returnType)) -@ LStateT initialType finalType returnType

public export
runLStateT : initialType -@ LStateT initialType finalType returnType -@ (LPair finalType returnType)
runLStateT i (MkLST f) = f i

public export
pure : a -@ LStateT t t a
pure x = MkLST (\st => st # x)

public export
(>>=) : LStateT i m a -@ ( a -@ LStateT m o b) -@ LStateT i o b
v >>= f =  MkLST  $ \i => let (a # m) = runLStateT i v in runLStateT a (f m)

||| some abstract interface, dummy
interface AbstractInterface (0 t : Nat -> Type) where
        run : LStateT (t m) (t m) (LVect n Nat) -@ (LVect n Nat)
  
||| someother abstract interface
interface OuterInterface (0 t : Nat -> Type) where
        |||some function from LVect to LStateT
        outerFunc : {n : Nat} -> {i : Nat} -> (LVect i Nat) -@ LStateT (t n) (t n) (LVect i Nat)

||| This works as should (I mean, it doesn't do anything, it's a dummy in this case, but compiles)
singleLayerFunc : OuterInterface t => (n : Nat) -> (m: Nat) -> LVect n Nat -@ LStateT (t (m)) (t (m)) (LVect n Nat)
singleLayerFunc 0 m [] = pure []
singleLayerFunc (S k) m qs = do
        lvec <- outerFunc {i = (S k)} {n = m} (qs)
        pure lvec

||| Now, we introduce some function on interface 1 - dummy in this case
innerFuncDummy : AbstractInterface t => (i : Nat) -> (m: Nat) -> LVect i Nat -@ LStateT (t m) (t m) (LVect i Nat)
innerFuncDummy 0 m any = pure any
innerFuncDummy (S k) m (q::qs) = pure (q::qs)   

||| Then, we attempt to first used the above, and then take the LVect out and move it up and do something with it in the outer interface
||| This fails to check that qs is linear
doubleLayerFunc : AbstractInterface t => OuterInterface t => (n : Nat) -> (m: Nat) -> LVect n Nat -@ LStateT (t (m)) (t (m)) (LVect n Nat)
doubleLayerFunc 0 m [] = pure []
doubleLayerFunc (S k) m qs = do
        lvec <- outerFunc (run $ innerFuncDummy {t} (S k) m (qs))
        pure lvec