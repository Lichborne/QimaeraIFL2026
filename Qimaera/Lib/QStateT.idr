module Qimaera.Lib.QStateT
import Control.Monad.State
import Utilities.LinearTypes
import Control.Linear.LIO
import Utilities.Lemmas
import public Qimaera.Lib   -- R, the QStateT type, its constructor and its runner live in the root module


%default total


||| Pure (linear)
public export
pure : (1 _ : a) -> QStateT t t a
pure x = MkQST (\st => pure1 (st # x))

||| Bind
public export
(>>=) : (1 _ : QStateT i m a) -> (1 _ : ((1 _ : a) -> QStateT m o b)) -> QStateT i o b
v >>= f = MkQST $ \i => runQStateT i v >>= \(a # m) => runQStateT a (f m)

||| mod (linear)
private
modify : ((1 _ : i) -> o) -> QStateT i o ()
modify f = MkQST $ \i => pure1 (f i # ())
