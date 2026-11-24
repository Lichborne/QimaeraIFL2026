module Qimaera.Lib.UStateT.Proofs

import Utilities.LinearTypes
import Qimaera.Lib
import Qimaera.Lib.UStateT

%default total

||| The abstract structure: pure and bind of UStateT keep every property of the state that the
||| computations they combine keep, so a property every operation keeps is kept by every unitary
||| computation built from them.

||| A linear pair as an ordinary pair, so that fst and snd apply. Used only in statements.
public export
unLPair : LPair a b -> (a, b)
unLPair (x # y) = (x, y)

||| Started in any state s with pre s, u ends in a state that satisfies post.
||| fst (unLPair (runUStateT s u)) is that final state. KeepsU is a data type, not a function,
||| so that Idris can infer pre, post and u from it.
public export
data KeepsU : {i, o, a : Type} -> (i -> Type) -> (o -> Type) -> UStateT i o a -> Type where
  MkKeepsU : ((s : i) -> pre s -> post (fst (unLPair (runUStateT s u)))) -> KeepsU pre post u

||| Applies a KeepsU proof to a starting state.
public export
keepsU : KeepsU pre post u -> (s : i) -> pre s -> post (fst (unLPair (runUStateT s u)))
keepsU (MkKeepsU k) = k

||| pure leaves the state unchanged (runUStateT s (pure x) reduces to s # x), so it keeps pre.
export
pureKeeps : {0 i, a : Type} -> {0 pre : i -> Type} -> (x : a) -> KeepsU pre pre (UStateT.pure {t = i} x)
pureKeeps x = MkKeepsU (\s, ok => ok)

||| bindKeeps as a function on states. v is not erased - we run it.
export
bindStep : {0 i, m, o, a, b : Type} -> {0 pre : i -> Type} -> {0 mid : m -> Type} -> {0 post : o -> Type}
        -> {v : UStateT i m a} -> {f : (1 _ : a) -> UStateT m o b}
        -> KeepsU pre mid v -> ((x : a) -> KeepsU mid post (f x))
        -> (s : i) -> pre s -> post (fst (unLPair (runUStateT s (v >>= f))))
bindStep kv kf s ok with (runUStateT s v) proof eq
  _ | (s' # x) = keepsU (kf x) s' (replace {p = \r => mid (fst (unLPair r))} eq (keepsU kv s ok))

||| If v takes pre to mid, and every f x takes mid to post, then v >>= f takes pre to post.
export
bindKeeps : {0 i, m, o, a, b : Type} -> {0 pre : i -> Type} -> {0 mid : m -> Type} -> {0 post : o -> Type}
         -> {v : UStateT i m a} -> {f : (1 _ : a) -> UStateT m o b}
         -> KeepsU pre mid v -> ((x : a) -> KeepsU mid post (f x)) -> KeepsU pre post (v >>= f)
bindKeeps kv kf = MkKeepsU (bindStep kv kf)