module Qimaera.Lib.UStateT.Proofs

import Utilities.LinearTypes
import Qimaera.Lib
import Qimaera.Lib.UStateT

%default total

||| The abstract structure: pure and bind of UStateT keep every property of the state that the
||| computations they combine keep, so a property every operation keeps is kept by every unitary
||| computation built from them.

public export
unLPair : LPair a b -> (a, b)
unLPair (x # y) = (x, y)

||| u takes states that satisfy pre to states that satisfy post.
public export
data KeepsU : {i, o, a : Type} -> (i -> Type) -> (o -> Type) -> UStateT i o a -> Type where
  MkKeepsU : ((s : i) -> pre s -> post (fst (unLPair (runUStateT s u)))) -> KeepsU pre post u

public export
keepsU : KeepsU pre post u -> (s : i) -> pre s -> post (fst (unLPair (runUStateT s u)))
keepsU (MkKeepsU k) = k

export
pureKeeps : {0 i, a : Type} -> {0 pre : i -> Type} -> (x : a) -> KeepsU pre pre (UStateT.pure {t = i} x)
pureKeeps x = MkKeepsU (\s, ok => ok)

export
bindStep : {0 i, m, o, a, b : Type} -> {0 pre : i -> Type} -> {0 mid : m -> Type} -> {0 post : o -> Type}
        -> {v : UStateT i m a} -> {f : (1 _ : a) -> UStateT m o b}
        -> KeepsU pre mid v -> ((x : a) -> KeepsU mid post (f x))
        -> (s : i) -> pre s -> post (fst (unLPair (runUStateT s (v >>= f))))
bindStep kv kf s ok with (runUStateT s v) proof eq
  _ | (s' # x) = ?w

export
bindKeeps : {0 i, m, o, a, b : Type} -> {0 pre : i -> Type} -> {0 mid : m -> Type} -> {0 post : o -> Type}
         -> {v : UStateT i m a} -> {f : (1 _ : a) -> UStateT m o b}
         -> KeepsU pre mid v -> ((x : a) -> KeepsU mid post (f x)) -> KeepsU pre post (v >>= f)
bindKeeps kv kf = MkKeepsU (bindStep kv kf)