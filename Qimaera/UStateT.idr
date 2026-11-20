module Qimaera.UStateT
import Control.Monad.State
import LinearTypes
import UnitaryLinear
import public Qimaera   -- the UStateT type, its constructor and its runner live in the root module




public export
pure : (1 _ : a) -> UStateT t t a
pure x = MkUST (\st => (st # x))

public export
(>>=) : (1 _ : UStateT i m a) -> (1 _ : ((1 _ : a) -> UStateT m o b)) -> UStateT i o b
v >>= f =  MkUST  $ \i => let (a # m) = runUStateT i v in runUStateT a (f m)

public export
modify : ((1 _ : i) -> o) -> UStateT i o ()
modify f = MkUST $ \i => (f i # ())
