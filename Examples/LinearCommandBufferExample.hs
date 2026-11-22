{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}

-- Proof of concept for the Qimaera/UnitaryOp resource pattern in a
-- non-quantum setting using GHC linear types. 
-- Barriers are inert, so no execution exhibits the hazard they prevent; 
-- this is a prototype to prove a point, not a real command buffer!
--
--
-- Plans build command syntax; submit interprets it.
-- The example combines hidden constructors and nominal roles, fresh ids,
-- linear use, and GADT/DataKinds indices.
--
-- Known limits:
--   * buffer length is runtime metadata, not a type index;
--   * buildPlan may return Dirty buffers;
--   * reads are not tracked;
--   * view barriers are whole-buffer barriers;
--   * CmdRep abstracts syntax, not arbitrary interpreters;
--   * splits do not nest and views cannot enter secondaries.
--   
--
-- ChatGPT was used for formatting, comments, and naming.

module Main
  ( main
  , Nat(..), SNat(..), Vec(..)
  , Access(..), Buffers(..), Buffer
  , Side(..), View, SplitPair(..)
  , CmdTree, CmdRep(..)
  , Uses(..), Plan, pureP, (>>>=)
  , Secondary
  , Built, runBuilt, submit
  , copyBuf, addConst, barrier, destroyBuf
  , splitBuf, addConstView, barrierView, rejoinBuf
  , applySecondaryOwn
  , buildPlan, buildClosedPlan, buildSecondary
  , mixedPlan, boxedPlan, destructionPlan, splitPlan
  ) where

import Prelude

------------------------------------------------------------
-- Type-level naturals and vectors
------------------------------------------------------------

data Nat = Z | S Nat

data SNat (n :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

data Vec (n :: Nat) a where
  VNil :: Vec 'Z a
  (:#) :: a -> Vec n a -> Vec ('S n) a

infixr 5 :#

------------------------------------------------------------
-- Heterogeneous buffer states
------------------------------------------------------------

data Access = Ready | Dirty

type family ReadyN (n :: Nat) :: [Access] where
  ReadyN 'Z     = '[]
  ReadyN ('S n) = 'Ready ': ReadyN n

-- Hidden constructor: clients cannot mint handles.
-- Nominal roles also block coercion between scopes or access states.
-- Length is runtime metadata used by splitBuf, not a type index.
type role Buffer nominal nominal
data Buffer s (access :: Access) where
  MkBuffer :: Int -> Int -> Buffer s access
  --              id     length

-- A list of buffers whose access states may differ.
type role Buffers nominal nominal
data Buffers s (states :: [Access]) where
  BNil :: Buffers s '[]
  (:&) :: Buffer s a %1
       -> Buffers s as %1
       -> Buffers s (a ': as)

infixr 5 :&

consumeBuffer :: Buffer s a %1 -> ()
consumeBuffer (MkBuffer _ _) = ()

consumeBuffers :: Buffers s as %1 -> ()
consumeBuffers BNil = ()
consumeBuffers (b :& bs) =
  case consumeBuffer b of
    () -> consumeBuffers bs

------------------------------------------------------------
-- Initial resources
------------------------------------------------------------

type Memory = [(Int, [Int])]

data FreshResult (n :: Nat) s where
  FreshResult
    :: Buffers s (ReadyN n) %1
    -> Memory
    -> FreshResult n s

freshFromValues
  :: Vec n [Int]
  -> Int
  -> FreshResult n s
freshFromValues VNil _ =
  FreshResult BNil []
freshFromValues (v :# vs) i =
  case freshFromValues vs (i + 1) of
    FreshResult bs mem ->
      FreshResult
        (MkBuffer i (length v) :& bs)
        ((i, v) : mem)

-- Used only to record secondaries; the length is a placeholder.
-- splitBuf may read it, but split/rejoin emits no range command, while
-- range operations are rejected by buildSecondary.
freshBuffers
  :: SNat n
  -> Int
  -> Buffers s (ReadyN n)
freshBuffers SZ _ =
  BNil
freshBuffers (SS n) i =
  MkBuffer i 1 :& freshBuffers n (i + 1)

------------------------------------------------------------
-- Command representation
------------------------------------------------------------

-- Abstracts command syntax. reindexRep assumes the representation
-- supports renaming, so this is not an arbitrary interpreter interface.
class CmdRep t where
  emptyRep     :: t
  appendRep    :: t -> t -> t
  copyRep      :: Int -> Int -> t
  addConstRep  :: Int -> Int -> t
  addRangeRep  :: Int -> Int -> Int -> Int -> t
  barrierRep   :: Int -> t
  destroyRep   :: Int -> t
  reindexRep   :: [Int] -> t -> t

data CmdTree
  = CEmpty
  | CCopy Int Int
  | CAddConst Int Int
  | CAddRange Int Int Int Int
  | CBarrier Int
  | CDestroy Int
  | CSeq CmdTree CmdTree
  | CReindexed [Int] CmdTree
  deriving Show

instance CmdRep CmdTree where
  emptyRep = CEmpty

  appendRep CEmpty y = y
  appendRep x CEmpty = x
  appendRep x y      = CSeq x y

  copyRep src dst       = CCopy src dst
  addConstRep k b       = CAddConst k b
  addRangeRep k b o len = CAddRange k b o len
  barrierRep b          = CBarrier b
  destroyRep b          = CDestroy b
  reindexRep ids op     = CReindexed ids op

------------------------------------------------------------
-- Plan construction
------------------------------------------------------------

data Uses = Whole | Ranged

-- 'Ranged marks plans whose commands depend on runtime ranges.
-- buildSecondary accepts only 'Whole. This does not track copyBuf's
-- length-changing behaviour.
type role Plan representational nominal nominal representational
data Plan t s (u :: Uses) a where
  Plan :: t -> a %1 -> Plan t s u a

pureP
  :: CmdRep t
  => a %1
  -> Plan t s u a
pureP x =
  Plan emptyRep x

(>>>=)
  :: CmdRep t
  => Plan t s u a %1
  -> (a %1 -> Plan t s u b) %1
  -> Plan t s u b
Plan p x >>>= k =
  case k x of
    Plan q y -> Plan (appendRep p q) y

infixl 1 >>>=

------------------------------------------------------------
-- Whole-buffer operations
------------------------------------------------------------

-- Reads src and writes dst; dst becomes Dirty.
-- Copy replaces the whole destination, so its returned length becomes srcLen.
-- In a secondary, applySecondaryOwn reconstructs output handles from the
-- caller's inputs, so this length change can be lost. A later splitBuf may
-- then use stale metadata. A type-level length would remove this defect.
copyBuf
  :: CmdRep t
  => Buffer s 'Ready %1
  -> Buffer s 'Ready %1
  -> Plan t s u
       (Buffers s '[ 'Ready, 'Dirty ])
copyBuf (MkBuffer src srcLen) (MkBuffer dst _dstLen) =
  Plan
    (copyRep src dst)
    (MkBuffer src srcLen
      :& MkBuffer dst srcLen
      :& BNil)

addConst
  :: CmdRep t
  => Int
  -> Buffer s 'Ready %1
  -> Plan t s u (Buffer s 'Dirty)
addConst k (MkBuffer b len) =
  Plan
    (addConstRep k b)
    (MkBuffer b len)

barrier
  :: CmdRep t
  => Buffer s 'Dirty %1
  -> Plan t s u (Buffer s 'Ready)
barrier (MkBuffer b len) =
  Plan
    (barrierRep b)
    (MkBuffer b len)

destroyBuf
  :: CmdRep t
  => Buffer s 'Ready %1
  -> Plan t s u ()
destroyBuf (MkBuffer b _) =
  Plan
    (destroyRep b)
    ()

------------------------------------------------------------
-- Disjoint views
------------------------------------------------------------

data Side = LeftSide | RightSide

-- MkView is not exported.
type role View nominal nominal nominal nominal
data View s p (side :: Side) (access :: Access) where
  MkView
    :: Int
    -> Int
    -> Int
    -> View s p side access
    -- buffer id, offset, length

-- The hidden p ties the halves to one split; Side fixes their roles,
-- and linearity prevents reuse. rejoinBuf needs both Ready. No nested splits.
data SplitPair s (leftState :: Access) (rightState :: Access) where
  SplitPair
    :: View s p 'LeftSide leftState %1
    -> View s p 'RightSide rightState %1
    -> SplitPair s leftState rightState

-- Split ownership into two adjacent ranges. Emits no command.
-- The ranges are computed from the runtime length.
splitBuf
  :: Buffer s 'Ready %1
  -> SplitPair s 'Ready 'Ready
splitBuf (MkBuffer b len) =
  let leftLen  = len `div` 2
      rightLen = len - leftLen
  in SplitPair
       (MkView b 0 leftLen)
       (MkView b leftLen rightLen)

addConstView
  :: CmdRep t
  => Int
  -> View s p side 'Ready %1
  -> Plan t s 'Ranged (View s p side 'Dirty)
addConstView k (MkView b off len) =
  Plan
    (addRangeRep k b off len)
    (MkView b off len)

-- Marks one view Ready but emits a whole-buffer barrier.
-- The 'Ranged index is conservative here: this command does not use the extent.
barrierView
  :: CmdRep t
  => View s p side 'Dirty %1
  -> Plan t s 'Ranged (View s p side 'Ready)
barrierView (MkView b off len) =
  Plan
    (barrierRep b)
    (MkView b off len)

-- Rejoin the two views produced by one split.
rejoinBuf
  :: SplitPair s 'Ready 'Ready %1
  -> Buffer s 'Ready
rejoinBuf
  (SplitPair
    (MkView b _ leftLen)
    (MkView _ _ rightLen)) =
      MkBuffer b (leftLen + rightLen)

------------------------------------------------------------
-- Secondary command buffers
------------------------------------------------------------

-- Reusable secondaries are Ready -> Ready and whole-buffer only.
type role Secondary representational nominal
data Secondary t (n :: Nat) where
  Secondary :: t -> Secondary t n

data IDsResult s as where
  IDsResult
    :: [Int]
    -> Buffers s as %1
    -> IDsResult s as

idsAndReturn
  :: Buffers s as %1
  -> IDsResult s as
idsAndReturn BNil =
  IDsResult [] BNil
idsAndReturn (MkBuffer i len :& bs) =
  case idsAndReturn bs of
    IDsResult ids bs' ->
      IDsResult
        (i : ids)
        (MkBuffer i len :& bs')

-- Range-dependent plans cannot be recorded as secondaries.
buildSecondary
  :: CmdRep t
  => SNat n
  -> (forall s.
        Buffers s (ReadyN n) %1
        -> Plan t s 'Whole (Buffers s (ReadyN n)))
  -> Secondary t n
buildSecondary n pattern =
  case pattern (freshBuffers n 0) of
    Plan body returned ->
      case consumeBuffers returned of
        () -> Secondary body

applySecondaryOwn
  :: CmdRep t
  => Buffers s (ReadyN n) %1
  -> Secondary t n %1
  -> Plan t s u (Buffers s (ReadyN n))
applySecondaryOwn buffers (Secondary body) =
  case idsAndReturn buffers of
    IDsResult ids buffers' ->
      Plan
        (reindexRep ids body)
        buffers'

------------------------------------------------------------
-- Complete command buffers
------------------------------------------------------------

data Built t where
  Built :: t -> Memory -> Built t

-- Generative boundary: ids and lengths come from the initial values,
-- and the rank-2 scope keeps handles local to this build.
-- The output state is unconstrained, so Dirty buffers may remain.
buildPlan
  :: CmdRep t
  => Vec n [Int]
  -> (forall s.
        Buffers s (ReadyN n) %1
        -> Plan t s u (Buffers s out))
  -> Built t
buildPlan values pattern =
  case freshFromValues values 0 of
    FreshResult bs initial ->
      case pattern bs of
        Plan body returned ->
          case consumeBuffers returned of
            () -> Built body initial

buildClosedPlan
  :: CmdRep t
  => Vec n [Int]
  -> (forall s.
        Buffers s (ReadyN n) %1
        -> Plan t s u ())
  -> Built t
buildClosedPlan values pattern =
  case freshFromValues values 0 of
    FreshResult bs initial ->
      case pattern bs of
        Plan body () ->
          Built body initial

------------------------------------------------------------
-- Examples
------------------------------------------------------------

type One = 'S 'Z

one :: SNat One
one = SS SZ

-- Returns a mixed typestate: Ready, Dirty, Ready.
mixedPattern
  :: CmdRep t
  => Buffers s '[ 'Ready, 'Ready, 'Ready ] %1
  -> Plan t s u
       (Buffers s '[ 'Ready, 'Dirty, 'Ready ])
mixedPattern
  (a :& b :& scratch :& BNil) =
    copyBuf a scratch >>>= \copied1 ->
      case copied1 of
        a1 :& scratchDirty1 :& BNil ->
          barrier scratchDirty1 >>>= \scratch1 ->
            addConst 5 scratch1 >>>= \scratchDirty2 ->
              barrier scratchDirty2 >>>= \scratch2 ->
                copyBuf scratch2 b >>>= \copied2 ->
                  case copied2 of
                    scratch3 :& bDirty :& BNil ->
                      pureP
                        (a1 :& bDirty :& scratch3 :& BNil)

mixedPlan :: Built CmdTree
mixedPlan =
  buildPlan
    ([10] :# [0] :# [0] :# VNil)
    mixedPattern

-- Rejected by linearity: destroyBuf consumes b.
--
-- badUseAfterDestroy
--   :: CmdRep t
--   => Buffer s 'Ready %1
--   -> Plan t s u (Buffer s 'Dirty)
-- badUseAfterDestroy b =
--   destroyBuf b >>>= \() ->
--     addConst 1 b

-- Rejected by the access index: copyBuf requires Ready.
--
-- badMissingBarrier
--   :: CmdRep t
--   => Buffer s 'Ready %1
--   -> Buffer s 'Ready %1
--   -> Plan t s u (Buffers s '[ 'Ready, 'Dirty ])
-- badMissingBarrier src dst =
--   addConst 1 src >>>= \srcDirty ->
--     copyBuf srcDirty dst

------------------------------------------------------------
-- Reusable secondary
------------------------------------------------------------

increment5
  :: Secondary CmdTree One
increment5 =
  buildSecondary one $ \(b :& BNil) ->
    addConst 5 b >>>= \dirty ->
      barrier dirty >>>= \ready ->
        pureP (ready :& BNil)

-- Rejected by the phase index: secondaries must be 'Whole.
--
-- rangedSecondary :: Secondary CmdTree One
-- rangedSecondary =
--   buildSecondary one $ \(b :& BNil) ->
--     case splitBuf b of
--       SplitPair left right ->
--         addConstView 1 left >>>= \leftDirty ->
--           barrierView leftDirty >>>= \leftReady ->
--             pureP (rejoinBuf (SplitPair leftReady right) :& BNil)

boxedPattern
  :: Buffers s '[ 'Ready, 'Ready ] %1
  -> Plan CmdTree s u
       (Buffers s '[ 'Ready, 'Ready ])
boxedPattern (a :& b :& BNil) =
  applySecondaryOwn
    (b :& BNil)
    increment5
  >>>= \bs ->
    case bs of
      b1 :& BNil ->
        pureP (a :& b1 :& BNil)

boxedPlan :: Built CmdTree
boxedPlan =
  buildPlan
    ([3] :# [10] :# VNil)
    boxedPattern

------------------------------------------------------------
-- Destruction
------------------------------------------------------------

destroyBoth
  :: Buffers s '[ 'Ready, 'Ready ] %1
  -> Plan CmdTree s u ()
destroyBoth (a :& b :& BNil) =
  destroyBuf a >>>= \() ->
    destroyBuf b

destructionPlan :: Built CmdTree
destructionPlan =
  buildClosedPlan
    ([7] :# [9] :# VNil)
    destroyBoth

------------------------------------------------------------
-- Disjoint-view example
------------------------------------------------------------

splitPattern
  :: Buffers s '[ 'Ready ] %1
  -> Plan CmdTree s 'Ranged
       (Buffers s '[ 'Ready ])
splitPattern (buf :& BNil) =
  case splitBuf buf of
    SplitPair left right ->
      addConstView 10 left >>>= \leftDirty ->
        addConstView 100 right >>>= \rightDirty ->
          barrierView leftDirty >>>= \leftReady ->
            barrierView rightDirty >>>= \rightReady ->
              pureP
                (rejoinBuf
                  (SplitPair leftReady rightReady)
                 :& BNil)

splitPlan :: Built CmdTree
splitPlan =
  buildPlan
    ([1,2,3,4] :# VNil)
    splitPattern

------------------------------------------------------------
-- Interpretation
------------------------------------------------------------

lookupMem :: Int -> Memory -> Maybe [Int]
lookupMem _ [] = Nothing
lookupMem key ((k,v):xs)
  | key == k  = Just v
  | otherwise = lookupMem key xs

writeMem
  :: Int
  -> [Int]
  -> Memory
  -> Maybe Memory
writeMem _ _ [] = Nothing
writeMem key value ((k,v):xs)
  | key == k  = Just ((k,value) : xs)
  | otherwise =
      case writeMem key value xs of
        Nothing  -> Nothing
        Just xs' -> Just ((k,v) : xs')

deleteMem :: Int -> Memory -> Maybe Memory
deleteMem _ [] = Nothing
deleteMem key ((k,v):xs)
  | key == k  = Just xs
  | otherwise =
      case deleteMem key xs of
        Nothing  -> Nothing
        Just xs' -> Just ((k,v) : xs')

slot :: [Int] -> Int -> Maybe Int
slot [] _ = Nothing
slot (x:_) 0 = Just x
slot (_:xs) n
  | n > 0     = slot xs (n - 1)
  | otherwise = Nothing

relabel :: [Int] -> CmdTree -> Maybe CmdTree
relabel _ CEmpty =
  Just CEmpty
relabel ids (CCopy a b) = do
  a' <- slot ids a
  b' <- slot ids b
  pure (CCopy a' b')
relabel ids (CAddConst k a) = do
  a' <- slot ids a
  pure (CAddConst k a')
relabel ids (CAddRange k a off len) = do
  a' <- slot ids a
  pure (CAddRange k a' off len)
relabel ids (CBarrier a) = do
  a' <- slot ids a
  pure (CBarrier a')
relabel ids (CDestroy a) = do
  a' <- slot ids a
  pure (CDestroy a')
relabel ids (CSeq x y) = do
  x' <- relabel ids x
  y' <- relabel ids y
  pure (CSeq x' y')
relabel outer (CReindexed inner body) = do
  composed <- mapM (slot outer) inner
  relabel composed body

modifyRange
  :: Int
  -> Int
  -> (Int -> Int)
  -> [Int]
  -> Maybe [Int]
modifyRange off len f xs
  | off < 0 || len < 0 = Nothing
  | off + len > length xs = Nothing
  | otherwise =
      let (pre, rest) = splitAt off xs
          (mid, post) = splitAt len rest
      in Just (pre ++ map f mid ++ post)

execTree :: CmdTree -> Memory -> Maybe Memory
execTree CEmpty mem =
  Just mem

execTree (CCopy src dst) mem = do
  value <- lookupMem src mem
  writeMem dst value mem

execTree (CAddConst k b) mem = do
  value <- lookupMem b mem
  writeMem b (map (+ k) value) mem

execTree (CAddRange k b off len) mem = do
  value <- lookupMem b mem
  value' <- modifyRange off len (+ k) value
  writeMem b value' mem

execTree (CBarrier _) mem =
  Just mem

execTree (CDestroy b) mem =
  deleteMem b mem

execTree (CSeq x y) mem = do
  mem' <- execTree x mem
  execTree y mem'

execTree (CReindexed ids body) mem = do
  body' <- relabel ids body
  execTree body' mem

runBuilt :: Built CmdTree -> Maybe Memory
runBuilt (Built body initial) =
  execTree body initial

submit :: Built CmdTree -> IO ()
submit built@(Built body initial) = do
  putStrLn ("Initial memory: " ++ show initial)
  putStrLn ("Commands: " ++ show body)
  case runBuilt built of
    Nothing ->
      putStrLn "Interpretation failed."
    Just final ->
      putStrLn ("Final memory: " ++ show final)

------------------------------------------------------------
-- Small checks
------------------------------------------------------------

check :: String -> Built CmdTree -> IO ()
check name built =
  case runBuilt built of
    Nothing ->
      error (name ++ ": interpretation failed")
    Just _ ->
      putStrLn (name ++ ": ok")

main :: IO ()
main = do
  check "mixed typestate" mixedPlan
  check "boxed secondary" boxedPlan
  check "destruction" destructionPlan
  check "disjoint views" splitPlan

  putStrLn "\nDisjoint-view result:"
  submit splitPlan
