module QuantumOp

import Data.Vect
import Data.Vect.Sort
import Data.Vect.Elem
import Data.Nat
import Decidable.Equality
import System.File
import Injection
import Matrix
import QuditMatrix
import Complex
import System.Random
import Lemmas
import QStateT
import Control.Linear.LIO
import LinearTypes
import UnitaryLinear
import UStateT
import Control.Linear.LIO
import UnitaryNoPrf

||| The Qubit type is used to identify individual qubits. The Nat argument is
||| used to uniquely identify a qubit. This type does *not* carry any quantum
||| state information. The constructor MkQubit is *private* in order to prevent
||| pattern matching by users of the library.
export
data Qubit : Type where
  MkQubit : (n : Nat) -> Qubit


public export 
interface UnitaryOp (0 t : Nat -> Type) where

  ||| Apply a unitary circuit to the Qubits specified by the Vect argument
  applyUnitary : {n : Nat} -> {i : Nat} -> 
                 (1 _ : LVect i Qubit) -> Unitary i -> UStateT (t n) (t n) (LVect i Qubit)

  ||| Apply a user-implemented unitary circuit to the Qubits specified by the Vect argument
  ||| since t n must implement unitaries, it works perfectly here.
  ||| liner in ownUnitary because this way results of "run" can be used
  applyUnitaryOwn : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> (1 ownUnitary : t i) -> UStateT (t n) (t n) (LVect i Qubit)

  ||| Apply the Hadamard gate to a single Qubit
  applyH : {n : Nat} -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 1 Qubit)
  applyH q = do
    [q1] <- applyUnitary {n} {i = 1} [q] HGate 
    pure [q1]

  ||| Apply a P gate to a single Qubit
  applyP : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 1 Qubit)
  applyP p q = do
    [q1] <- applyUnitary {n} {i = 1} [q] (PGate p)
    pure [q1]

  ||| Apply the CNOT gate to a pair of Qubits
  applyCNOT : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 2 Qubit)
  applyCNOT q1 q2 = do
    [q1,q2] <- applyUnitary {n} {i = 2} ([q1,q2]) CNOTGate
    pure (q1::q2::[])

  ||| apply a multiple controlled version of a UStateT built using the interface
  multipleControlUST: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1 controls : LVect i Qubit) -> (1 locations : LVect j Qubit) ->
                   (targetPattern : ((1_ :LVect j Qubit) -> UStateT (t j) (t j) (LVect j Qubit)))
                   -> UStateT (t n) (t n) (LVect (i + j) Qubit)


  ||| Abstract split application: helps with constructing circuits with parallel applications recursively (i.e. tensoring)
  applyParallel: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (t n) (t n) ((LVect i Qubit)))
                        -> (1_ : UStateT (t n) (t n) ((LVect j Qubit))) -> UStateT (t n) (t n) (LVect (i + j) Qubit)
 

  ||| Find the adjoint operation of a UStateT
  adjointUST: {n:Nat} -> (1_ : UStateT (t n) (t n) (LVect i Qubit)) -> (UStateT (t n) (t n) (LVect i Qubit))                 

  --withComputed: {n:Nat} -> (1_ : UStateT (t n) (t n) (LVect i Qubit)) -> (1_ : UStateT (t n) (t n) (LVect i Qubit)) 
  
  ||| sequence to the end
  run :  {i : Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LVect i Qubit) ) -> (LPair (t n) (LVect i Qubit))

  ||| Exort (t n) from UStateT, based on an initial t n. This needs us to be able to consume the LVect of Qubits, which requires the internal 
  ||| workings of qubits to which only QuantumOp has access, and it would be a circular import here. Thus, concrete 
  ||| implementations need to define this themselves
  exportSelf :  {i : Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LVect i Qubit)) -> (t n)

  ||| build a unitary in t n purely based on the pattern This requires that a function from an LVect of Qubits to a UStateT be given in order
  ||| to sequence the whole building of a unitary, depending on i and n (they will be equal, in fact).
  buildUnitary: {n:Nat} -> ((1_ : LVect n Qubit) -> (UStateT (t n) (t n) (LVect n Qubit))) -> (t n)

  ||| Default implementation would need the restricition that t must also implement UnitaryRun
  ||| therefore there is only the following commented pattern:
  --define
  --neutralRun : {n:Nat} -> (1_ : UStateT (t 0) (t n) (LVect n Qubit)) -> t n
  --define
      --buildUnitary f = neutralRun {t = t} {n=n} (do
        --qs <- supplyQubits {t = t} {n = 0} n
        --qsOut <- applyUStateT {t = t} {n = n} (f qs)
        --pure qsOut)

  --------------------- Additional Utilities -------------------------

  ||| apply a controlled version of a t i built using the interface
  ||| since there is a control we have to take from n, the UStateT used at most has n (if i = n) qubits 
  ||| i.e. it is one qubit smaller than the controlled version, which is therefore a larger UStateT
  ||| This will usually be fulfulled automatically by construction
  applyMultipleControlledOwn: {n : Nat} -> {i : Nat} -> {k:Nat} -> (1 controls : LVect (S k) Qubit) -> (1 targets : LVect i Qubit) -> (1 ownUnitary : t i)      
                   -> UStateT (t ((S k) + n)) (t ((S k) + n)) (LVect ((S k)+ i ) Qubit)

  ||| apply single controlled (t i)
  applyControlledOwn: {n : Nat} -> {i : Nat} -> (1 control : Qubit) -> (1 targets : LVect i Qubit) -> (1 ownUnitary : t i)      
                   -> UStateT (t (S n)) (t (S n)) (LVect (S i) Qubit)
  applyControlledOwn c targets uti = applyMultipleControlledOwn [c] targets uti

  ||| apply a controlled version of a UStateT built using the interface - default definition using the above
  controlUST: {n : Nat} -> {i : Nat} -> (1 control : Qubit) -> (1 locations : LVect i Qubit) ->
                   (targetPattern : ((1_ :LVect i Qubit) -> UStateT (t i) (t i) (LVect i Qubit)))
                   -> UStateT (t n) (t n) (LVect (S i) Qubit)
  controlUST c locs target = multipleControlUST [c] locs target

  ||| Abstract recombination. Helps with applying a split-computed unitary in QuantumOp
  combineAbs : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit))) 
                -> UStateT (t n) (t n) (LVect (i + j) Qubit)
  combineAbs ust = MkUST (f' ust) where 
    f' : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit))) 
                -> (1_ : t n) -> LPair (t n) (LVect (i + j) Qubit)
    f' ust ui = let (Builtin.(#) opOut (lvect # rvect)) = (runUStateT ( ui) ust) in do (Builtin.(#) opOut (LinearTypes.(++) lvect rvect))



------------- OTHER UTILITIES ------------
||| WHILE NOT STRICTLY A PART OF THE INTERFACE
||| IT IS HIGHLY RECOMMENDED THAT THESE 
||| UTILIZED, AS THEY MAKE LIFE A LOT EASIER
------------------------------------------

||| for exporting an instance opf the Unitary algebraic datatype based on the unitary build inside UStateT
||| this is not in general doable, as it depends on the structure of the specific t n and whether it can be translated into 
||| a value of Unitary n, because the proofs are necessary to build an instance of the type
export
exportUnitary : UnitaryOp t => {i : Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LVect i Qubit)) -> (Unitary n)

{- Apply the controlled version of a unitary. Implementations assume control goes at head of lvect list
applyControlWithSplitLVects : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : (LVect i Qubit)) -> (1_:(LVect j Qubit)) -> (1_: t (i+j))
--> UStateT (t (S n)) (t (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))


-}


|||combine split computation. This is raised in to UnitaryOp so that idris can see that appropriate conditions are fulfilled
export
combine : UnitaryOp t => {i:Nat} -> {j:Nat} ->  {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : LVect j Qubit) -> UStateT (t n) (t n) (LVect (i+j) Qubit)
combine {i=i} is js =  pure $ LinearTypes.(++) is js  

||| SWAP registers in parsing; an exchange of "wires", easy to make conditional 
export                           
swapRegistersSplit : UnitaryOp t => {i:Nat} -> {j:Nat}  -> {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : LVect j Qubit) -> UStateT (t n) (t n) (LPair (LVect j Qubit) (LVect i Qubit))
swapRegistersSplit qs rs = pure $ rs # qs

||| SWAP registers in parsing; an exchange of "wires", easy to make conditional 
export                           
swapRegistersSplitEq : UnitaryOp t =>  {i:Nat}  -> {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect i Qubit))
swapRegistersSplitEq qs rs = pure $ rs # qs

|||combine split computation, adding one qubit to the end
export
combineSingleR :UnitaryOp t =>  {i:Nat} -> {n : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
combineSingleR {i=Z} [] q =  pure $ [q]
combineSingleR {i=i} is q =  pure $ (rewrite sym $ lemmaplusOneRightHC {n = i} in (LinearTypes.(++) is [q]))

||| combine split computation, adding one qubit to the beginning
export
combineSingleL : UnitaryOp t => {i:Nat}  -> {n : Nat} -> (1 _ : Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LVect (S i) Qubit)
combineSingleL {i=Z} q [] =  pure $ [q]
combineSingleL {i=i} q is = pure $ (q :: is)

----------------Optionally definable functions ---------------
||| These are patterns for functions that are useful/helpful to 
||| define in concrete implementations, but are not part of the
||| interface.

||| Apply a user-implemented unitary circuit to the Qubits specified by the Vect argument  
||| This is essentially the same as just sequencing normally, and is mostly only representationally helpful     
export  
applyUnitaryAbs: UnitaryOp t => {n : Nat} -> {i : Nat} -> (1_ : UStateT (t n) (t n) (LVect i Qubit))      
                  -> UStateT (t n) (t n) (LVect i Qubit)


||| sequence to the end with split computation
export
runSplit : UnitaryOp t =>  {i : Nat} -> {j:Nat} -> (1_: (t n)) -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit)) ) 
            -> (LPair (t n) (LPair (LVect i Qubit) (LVect j Qubit)))
    
||| Abstract split application: Convenience function for avoiding proofs when dealing with multiple qubit list inputs/ancillae
export
applyWithSplitLVects : UnitaryOp t =>   {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit)))
                        -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit))

-------------------------------------------------------------------------------------------------------------
                      
%hint
export
singleQubit : (1 _ : LVect 1 Qubit)-> Qubit
singleQubit [q] = q

public export total
splitFirstUtil : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect 1 Qubit) (LVect i Qubit))
splitFirstUtil {i = Z} [] impossible
splitFirstUtil {i = Z} [as] = pure $ [as] # []
splitFirstUtil {i = (S Z)} [a,b] = pure $ [a] # [b]
splitFirstUtil {i = (S (S k))} (a::as) = do
    pure $ [a] # (as)

|||get the First qubit from a list of qubits
public export total
splitLastUtil : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect 1 Qubit))
splitLastUtil {i = Z} {n = n} [] impossible
splitLastUtil {i = Z} {n = n} [as] = pure $ [] # [as]
splitLastUtil {i = (S Z)} {n = n} [a,b] = pure $ [a] # [b]
splitLastUtil {i = (S (S k))} {n = n} (a::as) = do
    as # last <- splitLastUtil (as)
    pure $ (a :: as) # last
    
||| split qubits at index. careful with proofs 
public export
splitQubitsAt : UnitaryOp t => {i: Nat} -> {n : Nat} -> (k: Nat) -> {auto prf: LT k i} -> (1_ : LVect i Qubit) 
                            -> UStateT (t n) (t n) (LPair (LVect k Qubit) (LVect (minus i k) Qubit))
splitQubitsAt k [] = absurd prf
splitQubitsAt 0 any  = pure $ [] # (rewrite minusZeroRight i in any)
splitQubitsAt (S k) (a::as) = do
    as # ass <- splitQubitsAt k (as)
    pure $ ((a :: as)) # ass


||| split qubits at index
public export
splitQubitsInto : UnitaryOp t => {i: Nat} -> {n : Nat} -> (k: Nat) -> (r:Nat) -> {auto prf: k + r = i} -> (1_ : LVect i Qubit) 
                            -> UStateT (t n) (t n) (LPair (LVect k Qubit) (LVect r Qubit))
splitQubitsInto 0 0 [] = pure $ [] # []
splitQubitsInto 0 0 (a::as) impossible
splitQubitsInto {prf} 0 r any = (pure $ [] # (rewrite prf in any))
splitQubitsInto k 0 any = pure $ (rewrite sym $ plusZeroRightNeutral k in (rewrite prf in any)) # []
splitQubitsInto {prf = prf} {i = S h} (S k) (S r) (a::as) = do
    as # ass <- splitQubitsInto {prf = succInjective (rewrite plusSuccLeftSucc (k) (S r) in prf)}k (S r) (as)
    pure $ ((a :: as)) # ass

export                           
swapRegistersByLength : UnitaryOp t => {i:Nat} -> {j:Nat}  -> {n : Nat} -> (1 _ : LVect (i + j) Qubit) -> UStateT (t n) (t n) (LVect (j + i) Qubit)
swapRegistersByLength {i} {j} {n} qsrs = do 
  qs # rs <- splitQubitsInto i j qsrs 
  pure $ rs ++ qs

public export    
splitLVinto : (n : Nat) -> (k: Nat) -> (1_ : LVect (n + k) Qubit) 
                            -> (LPair (LVect n Qubit) (LVect k Qubit))
splitLVinto  0 0 [] = [] # []
splitLVinto 0 0 (a::as) impossible
splitLVinto  0 k any = [] # any
splitLVinto  n 0 any = (rewrite sym $ plusZeroRightNeutral n in any) # []
splitLVinto (S m) (S r) (a::as) = let as # ass = splitLVinto m (S r) (as) in (a::as) # ass


||| Find an element in a list : used to find the wire of a qubit
export
listIndex' : {n : Nat} -> Vect n Qubit -> Qubit -> Nat
listIndex' [] _ = 0
listIndex' (MkQubit x :: xs) (MkQubit k) = if x == k then 0 else S (listIndex' xs (MkQubit k))

||| The QuantumOp interface is used to abstract over the representation of a
||| quantum state. It is parameterised by the number of qubits it contains.
public export
interface QuantumOp (0 t : Nat -> Type) where

  ||| Prepare 'p' new qubits in state |00...0>
  newQubits : (p : Nat) -> QStateT (t n) (t (n+p)) (LVect p Qubit)
  newQubits Z     = rewrite plusZeroRightNeutral n in pure []
  newQubits (S k) = rewrite lemmaPlusSRight n k in do
    q <- newQubit
    qs <- newQubits k
    pure (q :: qs)

  ||| Prepare a single new qubit in state |0>
  newQubit : QStateT (t n) (t (S n)) Qubit
  newQubit = rewrite sym $ lemmaplusOneRight n in do
    [q] <- newQubits 1
    pure q
  
  ||| Apply a unitary circuit to the qubits specified by the Vector argument
  applyUST : {n : Nat} -> {i : Nat} -> (1_: UStateT (t n) (t n) (LVect i Qubit)) -> QStateT (t n) (t n) (LVect i Qubit)

  ||| Apply a unitary directly; kept around for convenience
  applyUnitaryDirectly : {n : Nat} -> {i : Nat} -> Unitary i -> (1_ : LVect i Qubit) -> QStateT (t n) (t n) (LVect i Qubit)

  ||| Apply Hadamard to specified qubit
  applyHQ: UnitaryOp t => {n : Nat} -> (1_ : Qubit) -> QStateT (t n) (t n) (LVect 1 Qubit)
  applyHQ q = do
              q <- applyUST {t = t} (applyH {t = t} {n = n } (q))
              pure q
  
  ||| Apply Hadamard to specified qubit
  applyPQ: UnitaryOp t => {n : Nat} -> (d:Double) -> (1_ : Qubit) -> QStateT (t n) (t n) (LVect 1 Qubit)
  applyPQ d q = do
              q <- applyUST {t = t} (applyP d {t = t} {n = n } (q))
              pure q

  ||| Apply  CNOT with specified contorl and target
  applyCNOTQ: UnitaryOp t => {n : Nat} -> (1_ : Qubit) -> (1_ : Qubit) -> QStateT (t n) (t n) (LVect 2 Qubit)
  applyCNOTQ c q = do
              cq <- applyUST {t = t} (applyCNOT {t = t} {n = n } c (q))
              pure cq

  ||| Measure some qubits in a quantum state
  measure : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QStateT (t (i + n)) (t n) (Vect i Bool)
  
  ||| Measure only one qubit
  measureQubit : {n : Nat} -> (1 _ : Qubit) -> QStateT (t (S n)) (t n) Bool
  measureQubit q = do
    [b] <- measure [q]
    pure b
  
  ||| Measure all qubits in a quantum state
  ||| Because of a bug in Idris2, we use the implementation below.
  ||| However, the implementation commented out is preferable if the bug gets fixed.
  measureAll : {n : Nat} -> (1 _ : LVect n Qubit) -> QStateT (t n) (t 0) (Vect n Bool)
  measureAll []        = pure []
  measureAll (q :: qs) = do
    b <- measureQubit q
    bs <- measureAll qs
    pure (b `consLin` bs)
  --measureAll qs = rewrite sym $ plusZeroRightNeutral n in measure qs
                          
  ||| Execute a quantum operation : start and finish with trivial quantum state
  ||| (0 qubits) and measure 'n' qubits in the process
  runQ : {n:Nat} -> QStateT (t 0) (t 0) (Vect n Bool) -> IO (Vect n Bool)

----- Qubit utilities, functions, and proofs----
private
qToNat : Qubit -> Nat
qToNat (MkQubit a) = a  

export
(+) : Qubit -> Qubit -> Qubit 
(+) (MkQubit a) (MkQubit b) = (MkQubit (plus a b))

Injective MkQubit where
  injective Refl = Refl

export
Uninhabited ( MkQubit Z =  MkQubit (S n)) where
  uninhabited Refl impossible

export
Uninhabited ( MkQubit (S n) =  MkQubit (Z))  where
  uninhabited Refl impossible

export
Uninhabited (( MkQubit a =  MkQubit b)) => Uninhabited  (( MkQubit (S a) =  MkQubit (S b))) where
  uninhabited Refl @{ab} = uninhabited @{ab} Refl

export
data LTEq  : (a, b : Qubit) -> Type where
  LTEqCons: LTE left right -> LTEq (MkQubit left) (MkQubit right)

export
Transitive Qubit LTEq where
  transitive (LTEqCons xy) (LTEqCons yz) =
    LTEqCons $ transitive xy yz


toLteqSucc : (LTEq (MkQubit (m)) (MkQubit (n))) -> (LTEq (MkQubit (S m)) (MkQubit (S n)))
toLteqSucc (LTEqCons x) = LTEqCons $ LTESucc x

fromLteqSucc : (LTEq (MkQubit (S m)) (MkQubit (S n))) -> (LTEq (MkQubit (m)) (MkQubit (n)))
fromLteqSucc (LTEqCons x) = LTEqCons $ fromLteSucc x

succNotLTEqzero : Not (LTEq (MkQubit (S n)) (MkQubit Z))
succNotLTEqzero LTEZero impossible
succNotLTEqzero (LTEqCons x) = absurd x 

export
isLTEq : (a, b : Qubit) -> Dec (LTEq a b)
isLTEq (MkQubit Z)  (MkQubit n) = Yes (LTEqCons LTEZero)
isLTEq (MkQubit (S k)) (MkQubit Z) = No (succNotLTEqzero)
isLTEq (MkQubit (S k)) (MkQubit (S j))
    = case isLTEq (MkQubit (k)) (MkQubit j) of
           No contra => No (contra . fromLteqSucc)
           Yes prf => Yes (toLteqSucc prf)


export
data LTq : Qubit -> Qubit -> Type where 
   LTqCons : LTEq (MkQubit (S left)) (MkQubit right) -> LTq (MkQubit (left)) (MkQubit right)

notltenotlt : (LTEq (MkQubit (S left)) (MkQubit right) -> Void) -> LTq (MkQubit (left)) (MkQubit right) -> Void
notltenotlt tovoid (LTqCons lte) = tovoid lte

export
isLTq : (l, r : Qubit) -> Dec (LTq l r)
isLTq (MkQubit left) (MkQubit right)= case isLTEq (MkQubit (S left)) (MkQubit right) of 
  Yes prf => Yes (LTqCons prf)
  No notprf => No (notltenotlt notprf)

--export
--decEqCong : (0 _ : Injective f) => Dec (x = y) -> Dec (f x = f y)
--decEqCong $ Yes prf   = Yes $ cong f prf
--decEqCong $ No contra = No $ \c => contra $ inj f c

export
DecEq Qubit where
  decEq (MkQubit Z)     (MkQubit Z)  = Yes Refl
  decEq (MkQubit (S n)) (MkQubit (S m)) = decEqCong $ decEq (S n) (S m)
  decEq (MkQubit Z)    (MkQubit (S _)) = No absurd
  decEq (MkQubit (S _)) (MkQubit Z)     = No absurd

export  
Consumable Qubit where
  consume (MkQubit Z) = ()
  consume (MkQubit (S k)) = ()

export  
Consumable Nat where
  consume (Z) = ()
  consume ((S k)) = ()

export 
consLinQ : (Qubit) -> (1_: Vect n Qubit) -> Vect (S n) Qubit
consLinQ (MkQubit Z) [] = [(MkQubit Z)]
consLinQ (MkQubit Z) (x :: xs) = (MkQubit Z) :: x :: xs
consLinQ ((MkQubit (S k))) [] = [MkQubit (S k)]
consLinQ (MkQubit (S k)) (x :: xs) = (MkQubit (S k)) :: x :: xs  

export
toVectQ : (1 _ : LVect n Qubit) -> (Vect n Qubit)
toVectQ [] = []
toVectQ ((MkQubit k):: xs) = (MkQubit k) `consLinQ` (toVectQ xs)

export
toLVectQ : (Vect n Nat) -> (LVect n Qubit)
toLVectQ [] = []
toLVectQ (k :: xs) = (MkQubit k) :: (toLVectQ xs)

export
toLVectQQ : (Vect n Qubit) -> (LVect n Qubit)
toLVectQQ [] = []
toLVectQQ (MkQubit k :: xs) = (MkQubit k) :: (toLVectQQ xs)

export
toVectN : (Vect n Qubit) -> (Vect n Nat)
toVectN [] = []
toVectN (MkQubit k :: xs) = (k) :: (toVectN xs)


export
fromVectN : (Vect n Nat) -> (Vect n Qubit)
fromVectN [] = []
fromVectN (k :: xs) = (MkQubit k) :: (fromVectN xs)

export
Consumable (Vect i elem) where 
    consume [] = ()
    consume (x :: xs) = ()

export
discardq : (1_ : LVect n Qubit) -> ()
discardq lvect = consume (toVectQ lvect)

export
unrestrictVec : (1 _ : Vect n Qubit) -> ((Vect n Qubit))
unrestrictVec [] = unrestricted $ MkBang []
unrestrictVec (x :: xs) =  (unrestricted $ MkBang (x)) :: (unrestricted $ MkBang (unrestrictVec xs))

export
toVectUnr : (1 _ : LVect n Qubit) -> ((Vect n Qubit))
toVectUnr any = unrestrictVec (toVectQ any)

export
toVectQNonLin : (1_ : Vect n Qubit) -> Pair (Vect n Qubit) (Vect n Qubit)
toVectQNonLin [] = MkPair [] []
toVectQNonLin ((MkQubit k):: xs) = let rest = (toVectQNonLin xs) in MkPair ((MkQubit k) :: (fst rest)) ((MkQubit k) :: (snd rest)) 

export
toNVect: (Vect i Nat) -> (Vect k Nat) -> (Vect n Nat) -> (Vect n Nat) 
toNVect _ _ [] = []
toNVect [] _ (x::xs) = (x::xs)
toNVect (x::xs) any (y::ys) = case isElem y (x::xs) of 
  No prf => case isElem y any of
    No prf => y :: (toNVect (x::xs) (any) ys)
    Yes prf => x :: (toNVect (x::xs) (x::any) ys)
  Yes prf => x :: (toNVect (xs) (x::any) ys)

export
toNVectQ: (Vect i Qubit) -> (Vect n Qubit) -> (Vect n Qubit) 
toNVectQ _ [] = []
toNVectQ [] (x::xs) = (x::xs)
toNVectQ xs ys = fromVectN $ toNVect (toVectN xs) [] (toVectN ys)

||| Remove an element at a given index in the vector
public export
removeElem : {n : Nat} -> Vect (S n) Qubit -> Nat -> Vect n Qubit
removeElem (x :: xs) 0 = xs
removeElem (x :: xs) (S k) = case xs of
                                  [] => []
                                  y :: ys => x :: removeElem xs k

||| make a neutral (0 to n) qubit vector
export
makeNeutralVect' : (n:Nat) -> Vect n Qubit
makeNeutralVect' Z = []
makeNeutralVect' (S k) = (MkQubit k) :: makeNeutralVect' k

||| make a basic vector (basically newqubitspointers n but only for vect)
private
makeNeutralVect : (n:Nat) -> Vect n Qubit
makeNeutralVect k = reverse $ makeNeutralVect' k

||| make a neutral (0 to n) qubit vector
private
makeNeutralVectN' : (n:Nat) -> Vect n Nat
makeNeutralVectN' Z = []
makeNeutralVectN' (S k) = ( k) :: makeNeutralVectN' k

||| make a basic vector (basically newqubitspointers n but only for vect)
export
makeNeutralVectN : (n:Nat) -> Vect n Nat
makeNeutralVectN k = reverse $ makeNeutralVectN' k

passDownForControl : {i:Nat} -> (1 _ : LVect i Qubit) -> LPair (LVect i Qubit) (LVect i Qubit) 
passDownForControl [] = [] # []
passDownForControl {i} xs = xs # (toLVectQQ $ makeNeutralVect i)

||| duplicate a qubit and take the natural number used to constructed out
export
qubitToNatPair : (1_ : Qubit) -> Pair Qubit Nat 
qubitToNatPair (MkQubit q) = ((MkQubit q), q)

export
distributeDupedLVect : (1 _ : LVect i Qubit) -> LPair (LVect i Qubit) (LVect i Qubit) 
distributeDupedLVect [] = [] # []
distributeDupedLVect (MkQubit k :: xs) = 
  let (q # v) = distributeDupedLVect xs in
  (MkQubit k :: q ) # (MkQubit k :: v)

export
distributeDupedLVectVect : (1 _ : LVect i Qubit) -> LFstPair (LVect i Qubit) (Vect i Nat) 
distributeDupedLVectVect [] = [] # []
distributeDupedLVectVect (MkQubit k :: xs) = 
  let (q # v) = distributeDupedLVectVect xs in
  (MkQubit k :: q ) # (k :: v)
  

||| this is unsafe in general, but safe for us
export
findInLinQ : {n:Nat} -> (q : Qubit) -> Vect (S n) Qubit -> (Vect n Qubit)
findInLinQ (MkQubit q) [] impossible
findInLinQ {n = Z} (MkQubit q) (MkQubit m :: xs) = []
findInLinQ {n = S r} (MkQubit q) (MkQubit m :: xs) = case decEq q m of
  Yes _ => xs
  No _ => (MkQubit m :: (findInLinQ {n = r} (MkQubit q) xs))
findInLinQ (MkQubit a) (x :: xs) = xs -- this is vacuous, but idris can't figure this out

export
predNat : Nat -> Nat
predNat Z     = 0
predNat (S k) = k

total export
searchFree : (used : List Nat) -> (candidate : Nat) -> Nat
searchFree used Z =
  if elem 0 used then 0 else 0
searchFree used (S k) =
  if elem (Prelude.S k) used
     then searchFree used k   -- total
     else S k

export
chooseSlot : (cap : Nat) -> (used : List Nat) -> (x : Nat) -> Nat
chooseSlot cap used x = searchFree used (min x (predNat cap))
   
export
clampUniqueWithCap :  {m : Nat} -> (cap : Nat) -> Vect m Nat -> Vect m Nat
clampUniqueWithCap {m} cap xs = snd (helper [] xs)
  where
    helper : List Nat -> Vect k Nat -> (List Nat, Vect k Nat)
    helper used [] = (used, [])
    helper used (x :: xs') =
      let y = chooseSlot cap used x
          used' = y :: used
          (used'' , ys) = helper used' xs'
      in (used'', y :: ys)


|||Find the smallest missing in an ordered vector
export
smallestMissing': (v: Vect n Nat) -> Nat
smallestMissing' [] = Z
smallestMissing' [Z] = S Z 
smallestMissing' [S k] = S (S k)
smallestMissing' (x::y::ys) = case decEq (S x) y of
       Yes _ => smallestMissing' (y::ys)
       No _ => (S x)
      
|||Find the smallest missing in an ordered vector
export
smallestMissing: (v: Vect n Nat) -> Nat
smallestMissing [] = Z
smallestMissing [Z] = S Z 
smallestMissing [S k] = S (S k)
smallestMissing (x::y::ys) = case x of 
  Z => case decEq (S x) y of
       Yes _ => smallestMissing' (y::ys)
       No _ => (S x)
  (S k) => Z

||| recalculate the counter
export
reCalculateCounter : {n:Nat} -> (v: Vect n Qubit) -> Nat
reCalculateCounter [] = 0
reCalculateCounter {n = S k} (x::xs) = smallestMissing (sort (toVectN (x::xs)))

||| add the indices of the new qubits to the vector in the SimulatedOp
private
newQubitsPointers : {n:Nat} -> (p : Nat) -> (counter : Nat) -> (v: Vect n Qubit) -> LFstPair (LVect p Qubit) (Pair (Vect p Qubit) Nat)
newQubitsPointers 0 counter _ = ([] # ([], counter))
newQubitsPointers {n} (S p) counter xs = let newcounter = (reCalculateCounter (MkQubit counter :: xs)) in
  let (q # (v, newcounter)) = newQubitsPointers p newcounter (MkQubit counter :: xs)
  in (MkQubit counter :: q) #  ((MkQubit counter :: v), newcounter)

private
newQubitsPointersOld : (p : Nat) -> (counter : Nat) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointersOld 0 _ = ([] # [])
newQubitsPointersOld (S p) counter = 
  let (q # v) = newQubitsPointersOld p (S counter)
  in (MkQubit counter :: q) #  (MkQubit counter :: v)  

||| add the indices of the new qubits to the vector in the SimulatedOp
private
newQubitsPointersNoCount : {n:Nat} -> (p : Nat)  -> (v: Vect n Qubit) -> LFstPair (LVect p Qubit) (Vect p Qubit)
newQubitsPointersNoCount 0 _ = ([] # ([]))
newQubitsPointersNoCount {n} (S p) xs = let newcounter = (reCalculateCounter (xs)) in
  let (q # v) = newQubitsPointersNoCount p (MkQubit newcounter :: xs)
  in (MkQubit newcounter :: q) #  ((MkQubit newcounter :: v))

||| Used for tests in Main.
private
mkQubitV : (from:Nat) -> (i:Nat) -> Vect i Qubit
mkQubitV Z Z = []
mkQubitV (S k) Z = []
mkQubitV Z (S k) = (MkQubit Z :: mkQubitV (S Z) k)     
mkQubitV (S n) (S k) = (MkQubit (S n) :: mkQubitV (S (S n)) k)  


||| Used for tests in Main.
private
mkQubitList : (from:Nat) -> (i:Nat) -> LVect i Qubit
mkQubitList Z Z = []
mkQubitList (S k) Z = []
mkQubitList Z (S k) = (MkQubit Z :: mkQubitList (S Z) k)     
mkQubitList (S n) (S k) = (MkQubit (S n) :: mkQubitList (S (S n)) k)  

----- IMPLEMENTATION OF QUANTUMSTATE: LINEAR-ALGEBRAIC SIMULATION -----------
public export
data SimulatedOp : Nat -> Type where
  MkSimulatedOp : {n : Nat} -> Matrix (power 2 n) 1 -> Unitary n -> Vect n Qubit -> Nat -> SimulatedOp n


export
neutralOp' : UnitaryOp t => {n:Nat} -> SimulatedOp n
neutralOp' {n} = (MkSimulatedOp (neutralIdPow n) (IdGate {n = n}) (makeNeutralVect n) n)

export
runNeutral' :  UnitaryOp t => {n : Nat} -> (1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect n Qubit) ) -> LPair (SimulatedOp n) (LVect n Qubit)
runNeutral' {n} ust = runUStateT (MkSimulatedOp (neutralIdPow n) (IdGate {n = n}) (makeNeutralVect n) n) ust

export
listIndex : (1 _ : SimulatedOp n) -> (1 _ : Qubit) -> LFstPair (LPair (SimulatedOp n) Qubit) Nat
listIndex (MkSimulatedOp qs us v counter) q = let (q, k) = qubitToNatPair q in
        (MkSimulatedOp qs us v counter # q) # (listIndex' v q)


lvectify : (1 _ : Vect i Qubit) -> (LVect i Qubit)
lvectify [] = []
lvectify (x :: xs) = LinearTypes.(::) x (lvectify xs)

mergeVects : (1 _ : Vect n Qubit) -> (1 _ : Vect i Qubit) -> ( LVect i Qubit)
mergeVects [] [] = []
mergeVects [] vect = lvectify vect
mergeVects (x :: xs) [] = mergeVects xs []
mergeVects (x :: xs) (y :: ys) = mergeVects xs (y::ys)

mergeLVects : (1 _ : LVect n Qubit) -> (1 _ : LVect i Qubit) -> (LVect i Qubit)
mergeLVects [] [] = []
mergeLVects [] lvect = lvect
mergeLVects (xs) [] = mergeVects (toVectQ xs) []
mergeLVects (xs) (ys) = mergeVects (toVectQ xs) (toVectQ ys)

||| Applying a circuit to some qubits
{-private
applyUnitary' : {n : Nat} -> {i : Nat} ->
  (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)) -> (1 _ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' ust (MkSimulatedOp qs un v counter) = let (Builtin.(#) opOut lvect) = (UnitaryOp.run' (MkSimulatedOp qs un v counter) ust) in do
  pure1 (Builtin.(#) opOut lvect)
-}
applyCirc : {n:Nat} -> Vect n Nat -> Unitary n -> (1 _ : SimulatedOp n) -> SimulatedOp n
applyCirc v IdGate qst = qst
applyCirc {n = n} v (H j g) st = 
  let k = indexLT j v 
      h = simpleTensor matrixH n k
      MkSimulatedOp qst urest q counter = applyCirc v g st
  in MkSimulatedOp (h `matrixMult` qst) IdGate q counter
applyCirc {n = n}  v (P p j g) st = 
  let k = indexLT j v
      ph = simpleTensor (matrixP p) n k
      MkSimulatedOp qst urest q counter = applyCirc v g st
  in MkSimulatedOp (ph `matrixMult` qst) IdGate q counter
applyCirc {n = n} v (CNOT c t g) st = 
  let kc = indexLT c v
      kt = indexLT t v
      cn =  tensorCNOT n kc kt
      MkSimulatedOp qst urest q counter = applyCirc v g st
  in MkSimulatedOp (cn `matrixMult` qst) IdGate q counter

applyUnitary' : {n : Nat} -> {i : Nat} -> ( 1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> (1 _ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitary' ust (MkSimulatedOp qs un v counter) = 
  let (MkSimulatedOp qsOut unOut vOut counterOut) # lvect = (runUStateT (MkSimulatedOp qs un v counter) ust) in
  let --(qs # v') # ind = listIndices opOut lvect 
      qs2 = applyCirc (toVectN v) unOut (MkSimulatedOp qsOut unOut vOut counterOut)
  in pure1 (Builtin.(#) qs2  lvect)

    
||| Apply a unitary circuit to a SimulatedOp Alt
export
applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
  ( 1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> QStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitarySimulated ust = MkQST (applyUnitary' ust)

applyUDirectlySimulated' : {n : Nat} -> {i : Nat} -> Unitary i -> (1_ : LVect i Qubit) -> (1_ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUDirectlySimulated' ui li (MkSimulatedOp qs un v counter) = 
                      let lvOut # vect = distributeDupedLVectVect li in
                          let unew # _ = applySafe ui IdGate vect in
                              let qs2 = applyCirc (toVectN v) unew (MkSimulatedOp qs un v counter) in
                                  pure1 (qs2 # lvOut)


applyUDirectlySimulated : {n : Nat} -> {i : Nat} -> Unitary i -> (1_ : LVect i Qubit) -> QStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUDirectlySimulated ui li  = MkQST (applyUDirectlySimulated' ui li)

||| Auxiliary function for applying a circuit to some qubits
private
applyUnitaryAbs' : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) ->
  (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)) -> (1 _ : SimulatedOp n) -> R (LPair (SimulatedOp n) (LVect i Qubit))
applyUnitaryAbs' lvectIn ust (MkSimulatedOp qs un v counter) = let (Builtin.(#) opOut lvect) = (runUStateT (MkSimulatedOp qs un v counter) ust) in do
  pure1 (Builtin.(#) opOut (mergeLVects lvect lvectIn))

||| Apply a unitary circuit to a SimulatedOp
export
applyUnitarySimulatedAbs : {n : Nat} -> {i : Nat} -> (1_ : LVect i Qubit) ->
  ( 1 _ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit) ) -> QStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit)
applyUnitarySimulatedAbs lvect q = MkQST (applyUnitaryAbs' lvect q)


||| Auxiliary function for measurements
private
measure' : {n : Nat} -> (i : Nat) ->
           (1 _ : SimulatedOp (S n)) ->
           R (LFstPair (SimulatedOp n) Bool)
measure' {n} i (MkSimulatedOp v un w counter) = do
  let projector0 = simpleTensor matrixKet0Bra0 (S n) i
  let projection0 = projector0 `matrixMult` v
  let norm20 = normState2 projection0
  let projector1 = simpleTensor matrixKet1Bra1 (S n) i
  let projection1 = projector1 `matrixMult` v
  let norm21 = normState2 projection1
  let newQubits = removeElem w i
  randnb <- liftIO1 randomIO
  if randnb < norm20
     then do
       let proj = multScalarMatrix (inv (sqrt norm20) :+ 0) projection0
       pure1 (MkSimulatedOp (projectState {n} proj i False) IdGate newQubits counter # False)
     else do
       let proj = multScalarMatrix (inv (sqrt norm21) :+ 0) projection1
       pure1 (MkSimulatedOp (projectState {n} proj i True) IdGate newQubits counter # True)

||| Helper, so that we only have to recalculate the counter once
private
measureQubits'' : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) ->
                 (1 _ : SimulatedOp (i + n)) -> R (LPair (SimulatedOp n) (Vect i Bool))
measureQubits'' [] qs = pure1 (qs # [])
measureQubits'' (x :: xs) qs = 
  let (qs' # q) # y = listIndex qs x in
    let (q, k) = qubitToNatPair q in 
      do
      (s # b) <- measure' y qs'
      (s1 # bs) <- measureQubits'' xs s
      case bs of 
          [] => pure1 (s1 # [b])
          (b' :: bs') => pure1 (s1 # (b :: b' :: bs'))

||| Auxiliary function for measurements
private
measureQubits' : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) ->
                 (1 _ : SimulatedOp (i + n)) -> R (LPair (SimulatedOp n) (Vect i Bool))
measureQubits' [] qs = pure1 (qs # [])
measureQubits' (x :: xs) qs = 
  let (qs' # q) # y = listIndex qs x in
    let (q, k) = qubitToNatPair q in 
      do
      (s # b)<- measure' y qs'
      (MkSimulatedOp stfin unfin vfin counter # bs) <- measureQubits'' xs s
      case bs of 
          [] => pure1 (MkSimulatedOp stfin unfin vfin (reCalculateCounter vfin) # [b])
          (b' :: bs') => pure1 (MkSimulatedOp stfin unfin vfin (reCalculateCounter vfin) # (b :: b' :: bs'))

------- SIMULATE CIRCUITS : OPERATIONS ON QUANTUM STATES ------

||| Add new qubits to a Quantum State
private
newQubitsSimulated : (p : Nat) -> QStateT (SimulatedOp n) (SimulatedOp (n+p)) (LVect p Qubit)
newQubitsSimulated p = MkQST (newQubits' p) where
  newQubits' : (q : Nat) -> (1 _ : SimulatedOp m) -> R (LPair (SimulatedOp (m + q)) (LVect q Qubit))
  newQubits' q (MkSimulatedOp qs un v counter) =
    let s' = toTensorBasis (ket0 q)
        (qubits # (v', newcounter))= newQubitsPointers q counter v
    in pure1 (MkSimulatedOp (tensorProductVect qs s') ( un # IdGate )  (v ++ v') (newcounter) # qubits)


private
newQubitsSimulatedUST : (p : Nat) -> UStateT (SimulatedOp n) (SimulatedOp (n+p)) (LVect p Qubit)
newQubitsSimulatedUST p = MkUST (newQubits' p) where
  newQubits' : (q : Nat) -> (1 _ : SimulatedOp m) -> (LPair (SimulatedOp (m + q)) (LVect q Qubit))
  newQubits' q (MkSimulatedOp qs un v counter) =
    let s' = toTensorBasis (ket0 q)
        (qubits # (v', newcounter))= newQubitsPointers q counter v
    in (MkSimulatedOp (tensorProductVect qs s') ( un # IdGate )  (v ++ v') (newcounter) # qubits)   

||| Measure some qubits in a quantum state
export
measureSimulated : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QStateT (SimulatedOp (i + n)) (SimulatedOp n) (Vect i Bool)
measureSimulated v = MkQST (measureQubits' v)


%hint
export
qubitlvect : (1_ : Qubit) -> LVect 1 Qubit
qubitlvect q = [q]


||| Run all simulations : start with 0 qubit and measure all qubits at the end (end with 0 qubit)
export
runSimulated : {n:Nat} -> QStateT (SimulatedOp 0) (SimulatedOp 0) (Vect n Bool) -> IO (Vect n Bool)
runSimulated s = LIO.run (do
  ((MkSimulatedOp st un w c) # v) <- runQStateT (MkSimulatedOp [[1]] IdGate [] 0) s
  case v of 
       [] => pure []
       (x :: xs) => pure (x :: xs))
 

export
QuantumOp SimulatedOp where
  newQubits    = newQubitsSimulated
  applyUST = applyUnitarySimulated
  applyUnitaryDirectly = applyUDirectlySimulated
  measure      = measureSimulated
  runQ          = runSimulated


--------------------------- BinarySimulatedOp with functions that only QuantumOp has access to-------------------

||| The counter (Nat) here is a count for how many functions we have! We recalculate qubit counters anyway.
public export
data BinarySimulatedOp : Nat -> Type where
  MkBinarySimulatedOp : {n : Nat} -> Unitary n -> Vect n Qubit -> Nat -> String -> BinarySimulatedOp n

||| Reset string
export 
resetNStr: {n:Nat} -> Vect n Nat -> String
resetNStr []  =    ""
resetNStr (x::xs) = "\tcircuit.reset("++ show x ++")\n" ++ resetNStr xs


||| Add the string for resetting qubits  
export
addQubitsResetStr: {n : Nat} -> String -> (counter:Nat) -> Vect n Nat -> String
addQubitsResetStr str counter v =
    let sOut = str ++ "\ndef Function"++ show counter++"(circuit):  \n" 
             ++ resetNStr v ++  
             "\treturn circuit\n\n" in
              sOut

||| New qubits in BinarySimulatedOp
export
newQubitsSimulatedCirc : (p : Nat) -> QStateT (BinarySimulatedOp n) (BinarySimulatedOp (n+p)) (LVect p Qubit)
newQubitsSimulatedCirc p = MkQST (newQubits' p) where
  newQubits' : (q : Nat) -> (1 _ : BinarySimulatedOp m) -> R (LPair (BinarySimulatedOp (m + q)) (LVect q Qubit))
  newQubits' q (MkBinarySimulatedOp un v counter str) =
    let (qubits # (v'))= newQubitsPointersNoCount q  v in 
      let strOut = addQubitsResetStr str counter (toVectN v') in
        pure1 (MkBinarySimulatedOp ( un # IdGate ) (v ++ v') (S counter) (strOut) # qubits)

||| new qubits for UnitaryRun
private
newQubitsBinSimulatedUST : (p : Nat) -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp (n+p)) (LVect p Qubit)
newQubitsBinSimulatedUST p = MkUST (newQubits' p) where
  newQubits' : (q : Nat) -> (1 _ : BinarySimulatedOp m) -> (LPair (BinarySimulatedOp (m + q)) (LVect q Qubit))
  newQubits' q (MkBinarySimulatedOp un v counter str) =
    let s' = toTensorBasis (ket0 q)
        (qubits # (v', newcounter))= newQubitsPointers q counter v
    in (MkBinarySimulatedOp ( un # IdGate )  (v ++ v') (newcounter) str# qubits)  

---------------------------------------------------------
|||The RunUnitaryOp Abstract Interface
---------------------------------------------------------
public export
interface RunUnitaryOp (0 t : Nat -> Type) where

  ||| Prepare 'p' new qubits in state |00...0>
  supplyQubits : {n:Nat} -> (p : Nat) -> UStateT (t n) (t (n+p)) (LVect p Qubit)
  supplyQubits Z     = rewrite plusZeroRightNeutral n in pure []
  supplyQubits (S k) = rewrite lemmaPlusSRight n k in do
    q <- supplyQubit
    qs <- supplyQubits k
    pure (q :: qs)

  ||| Prepare a single new qubit in state |0>
  supplyQubit : {n:Nat} -> UStateT (t n) (t (S n)) Qubit
  supplyQubit = rewrite sym $ lemmaplusOneRight n in (do
    [q] <- supplyQubits 1
    pure q)
  
  ||| Apply a unitary circuit to the qubits specified by the Vector argument
  applyUStateT : {n : Nat} -> {i : Nat} -> (1_: UStateT (t n) (t n) (LVect i Qubit)) -> UStateT (t n) (t n) (LVect i Qubit)

  ||| Apply a unitary circuit to the qubits specified by the Vector argument
  applyUStateTSplit : {n : Nat} -> {i : Nat} ->  (1_: UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect j Qubit))) -> UStateT (t n) (t n) (LVect (i+j) Qubit)
     
  ||| parse RunUnitaryOp to build the unitary transformation in t.
  runUnitaryOp : {n:Nat} -> UStateT (t 0) (t n) (LVect n Qubit) -> (t n)




idUp :  {m:Nat} -> (1 _ : Unitary m) -> (q : Nat) -> Unitary (m + q)
idUp um Z = rewrite plusZeroRightNeutral m in um
idUp um (S k) = um # (IdGate {n = (S k)})

idUpNoPrf :  {m:Nat} -> (1 _ : UnitaryNoPrf m) -> (q : Nat) -> UnitaryNoPrf (m + q)
idUpNoPrf um Z = rewrite plusZeroRightNeutral m in um
idUpNoPrf um (S k) = um # (IdGate {n = (S k)})

export
newQubitsUST : {n:Nat} -> (p : Nat) -> UStateT (Unitary n) (Unitary (n+p)) (LVect p Qubit)
newQubitsUST p = MkUST (newQubits' p) where
  newQubits' : {m:Nat} -> (q : Nat) -> (1 _ : Unitary m) ->(LPair (Unitary (m + q)) (LVect q Qubit))
  newQubits' {m} q un = 
    let (qubits # v') = newQubitsPointersNoCount q (mkQubitV 0 m)
    in (idUp un q # qubits)

export
newQubitsUSTNoPrf : {n:Nat} -> (p : Nat) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf (n+p)) (LVect p Qubit)
newQubitsUSTNoPrf p = MkUST (newQubits' p) where
  newQubits' : {m:Nat} -> (q : Nat) -> (1 _ : UnitaryNoPrf m) ->(LPair (UnitaryNoPrf (m + q)) (LVect q Qubit))
  newQubits' {m} q un = 
    let (qubits # v') = newQubitsPointersNoCount q (mkQubitV 0 m)
    in (idUpNoPrf un q # qubits)



-------------Unitary implementation of UnitaryRun --------------

||| Helper for Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTR': {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))      
                   -> (1 _ : Unitary n) -> LPair (Unitary n) (LVect i Qubit)
applyUSTR' ust un = 
  let (uOut # lvect) = runUStateT IdGate ust in
        let unew = UnitaryLinear.compose uOut un in
          do unew # (lvect)

||| Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTSimulatedR : {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))      
                   -> UStateT (Unitary n) (Unitary n) (LVect i  Qubit)
applyUSTSimulatedR ust = MkUST (applyUSTR' ust )

||| Helper for Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTSplit': {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> (1 _ : Unitary n) -> LPair (Unitary n) (LVect (i + j) Qubit)
applyUSTSplit' ust un = 
  let (uOut # (lvi # lvj)) = runUStateT IdGate ust in
        let unew = UnitaryLinear.compose uOut un in
          do unew # (lvi ++ lvj)

||| Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTSimulatedSplit : {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> UStateT (Unitary n) (Unitary n) (LVect (i + j) Qubit)
applyUSTSimulatedSplit ust = MkUST (applyUSTSplit' ust )


runUnitaryOp' : {n:Nat} -> UStateT (Unitary 0) (Unitary n) (LVect n Qubit) -> (Unitary n)
runUnitaryOp' ust = let un # lv = runUStateT IdGate ust in
                      let () = discardq lv in
                        un


public export
RunUnitaryOp Unitary where
  supplyQubits = newQubitsUST
  applyUStateT = applyUSTSimulatedR
  runUnitaryOp = runUnitaryOp'
  applyUStateTSplit = applyUSTSimulatedSplit


-------------UnitaryNoPrf implementation of UnitaryRun --------------

||| Helper for Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTRNoPrf': {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))      
                   -> (1 _ : UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LVect i Qubit)
applyUSTRNoPrf' {n} ust un = 
  let (uOut # lvect) = runUStateT (UnitaryNoPrf.IdGate {n = n}) ust in
        let unew = UnitaryNoPrf.compose uOut un in
          unew # (lvect)

||| UnitaryNoPrfimplementation of abstract UnitaryNoPrfapplication (that is, whatever one built using UStateT)
applyUSTSimulatedRNoPrf : {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))      
                   -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i  Qubit)
applyUSTSimulatedRNoPrf ust = MkUST (applyUSTRNoPrf' ust )

||| Helper for UnitaryNoPrfimplementation of abstract UnitaryNoPrfapplication (that is, whatever one built using UStateT)
applyUSTSplitNoPrf': {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> (1 _ : UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LVect (i + j) Qubit)
applyUSTSplitNoPrf' ust un = 
  let (uOut # (lvi # lvj)) = runUStateT UnitaryNoPrf.IdGate ust in
        let unew = UnitaryNoPrf.compose uOut un in
          unew # (lvi ++ lvj)

||| UnitaryNoPrfimplementation of abstract UnitaryNoPrfapplication (that is, whatever one built using UStateT)
applyUSTSimulatedSplitNoPrf : {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect (i + j) Qubit)
applyUSTSimulatedSplitNoPrf ust = MkUST (applyUSTSplitNoPrf' ust )


runUnitaryOpNoPrf' : {n:Nat} -> UStateT (UnitaryNoPrf 0) (UnitaryNoPrf n) (LVect n Qubit) -> (UnitaryNoPrf n)
runUnitaryOpNoPrf' ust = let un # lv = runUStateT IdGate ust in
                      let () = discardq lv in
                        un


public export
RunUnitaryOp UnitaryNoPrf where
  supplyQubits = newQubitsUSTNoPrf
  applyUStateT = applyUSTSimulatedRNoPrf
  runUnitaryOp = runUnitaryOpNoPrf'
  applyUStateTSplit = applyUSTSimulatedSplitNoPrf


-------------SimulatedOp implementation of UnitaryRun --------------

||| Helper for SimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTSimOp': {n : Nat} -> {i : Nat} -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit))      
                   -> (1 _ : SimulatedOp n) -> LPair (SimulatedOp n) (LVect i Qubit)
applyUSTSimOp' ust (MkSimulatedOp qs un vn count) = 
  let ((MkSimulatedOp qs uOut vn count) # lvect) = runUStateT (MkSimulatedOp qs IdGate vn count) ust in
        let unew = UnitaryLinear.compose uOut un in
          do (MkSimulatedOp qs unew vn count) # (lvect)

||| SimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTSimulatedSimOp : {n : Nat} -> {i : Nat} -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LVect i Qubit))      
                   -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect i  Qubit)
applyUSTSimulatedSimOp ust = MkUST (applyUSTSimOp' ust )

||| Helper for SimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTSplitSimOp': {n : Nat} -> {i : Nat} -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> (1 _ : SimulatedOp n) -> LPair (SimulatedOp n) (LVect (i + j) Qubit)
applyUSTSplitSimOp' ust (MkSimulatedOp qs un vn count) = 
  let ((MkSimulatedOp qs uOut vn count) # (lvi # lvj)) = runUStateT (MkSimulatedOp qs IdGate vn count) ust in
        let unew = UnitaryLinear.compose uOut un in
          do (MkSimulatedOp qs unew vn count) # (lvi ++ lvj)

||| SimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTSimulatedSplitSimOp : {n : Nat} -> {i : Nat} -> (1_ : UStateT (SimulatedOp n) (SimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> UStateT (SimulatedOp n) (SimulatedOp n) (LVect (i + j) Qubit)
applyUSTSimulatedSplitSimOp ust = MkUST (applyUSTSplitSimOp' ust )


runUnitaryOpSimOp : {n:Nat} -> UStateT (SimulatedOp 0) (SimulatedOp n) (LVect n Qubit) -> (SimulatedOp n)
runUnitaryOpSimOp {n} ust = let un # lv = runUStateT (MkSimulatedOp (neutralIdPow 0) IdGate (makeNeutralVect 0) 0) ust in
                      let () = discardq lv in
                        un


public export
RunUnitaryOp SimulatedOp where
  supplyQubits = newQubitsSimulatedUST
  applyUStateT = applyUSTSimulatedSimOp
  runUnitaryOp = runUnitaryOpSimOp
  applyUStateTSplit = applyUSTSimulatedSplitSimOp


-------------BinarySimulatedOp implementation of UnitaryRun --------------

||| Helper for BinarySimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTBinSimOp': {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> (1 _ : BinarySimulatedOp n) -> LPair (BinarySimulatedOp n) (LVect i Qubit)
applyUSTBinSimOp' ust (MkBinarySimulatedOp un vn count str) = 
  let ((MkBinarySimulatedOp uOut vn count str) # lvect) = runUStateT (MkBinarySimulatedOp IdGate vn count str) ust in
        let unew = UnitaryLinear.compose uOut un in
          do (MkBinarySimulatedOp unew vn count str) # (lvect)

||| BinarySimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTBinSimulatedSimOp : {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i  Qubit)
applyUSTBinSimulatedSimOp ust = MkUST (applyUSTBinSimOp' ust )

||| Helper for BinarySimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTBinSplitSimOp': {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> (1 _ : BinarySimulatedOp n) -> LPair (BinarySimulatedOp n) (LVect (i + j) Qubit)
applyUSTBinSplitSimOp' ust (MkBinarySimulatedOp un vn count str) = 
  let ((MkBinarySimulatedOp uOut vn count str) # (lvi # lvj)) = runUStateT (MkBinarySimulatedOp IdGate vn count str) ust in
        let unew = UnitaryLinear.compose uOut un in
          do (MkBinarySimulatedOp unew vn count str) # (lvi ++ lvj)

||| BinarySimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTBinSimulatedSplitSimOp : {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect (i + j) Qubit)
applyUSTBinSimulatedSplitSimOp ust = MkUST (applyUSTBinSplitSimOp' ust )


runUnitaryOpBinSimOp : {n:Nat} -> UStateT (BinarySimulatedOp 0) (BinarySimulatedOp n) (LVect n Qubit) -> (BinarySimulatedOp n)
runUnitaryOpBinSimOp {n} ust = let un # lv = runUStateT (MkBinarySimulatedOp IdGate (makeNeutralVect 0) 0 "") ust in
                      let () = discardq lv in
                        un

||| add a string that describes a new function to string
addNamedFunc: {n : Nat} -> (name:String) -> String -> (counter:Nat) -> Unitary n -> String
addNamedFunc name str counter g =
  let s = unitarytoQVis g in
  let sOut = str ++ "\ndef "++ name ++"(circuit):  \n" 
             ++ (s) ++
             "\treturn circuit\n\n" in
              sOut


||| Helper for BinarySimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTBox': {n : Nat} -> {i : Nat} -> (String) -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> (1 _ : BinarySimulatedOp n) -> LPair (BinarySimulatedOp n) (LVect i Qubit)
applyUSTBox' strIn ust (MkBinarySimulatedOp un vn count str) = 
  let ((MkBinarySimulatedOp uOut vnew count str) # lvect) = runUStateT (MkBinarySimulatedOp IdGate vn count str) ust in
        let strnew = addNamedFunc strIn str count uOut in
          let unew = UnitaryLinear.compose uOut un in
            do ((MkBinarySimulatedOp unew vnew (S count) strnew) # (lvect))


||| BinarySimulatedOp implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTBox : {n : Nat} -> {i : Nat} -> (String) -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i  Qubit)
applyUSTBox str ust = MkUST (applyUSTBox' str ust )

||| add a string that describes a new function to string
addStringFunc: {n : Nat} -> String -> (counter:Nat) -> Unitary n -> String
addStringFunc str counter g =
  let s = unitarytoQVis g in
  let sOut = str ++ "\ndef Function"++ show counter++"(circuit):  \n" 
             ++ (s) ++
             "\treturn circuit\n\n" in
              sOut

||| Helper for BinarySimulatedOp impolementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTBin': {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> (1 _ : BinarySimulatedOp n) -> R (LPair (BinarySimulatedOp n) (LVect i Qubit))
applyUSTBin' ust (MkBinarySimulatedOp un v counter str) = 
  let ((MkBinarySimulatedOp unrun vnew vacuousCounter str) # lvect) = runUStateT (MkBinarySimulatedOp IdGate v counter str) ust in
      let strnew = addStringFunc str counter unrun in
        let unew = compose unrun un in
          do pure1 ((MkBinarySimulatedOp unew vnew (S counter) strnew) # (lvect))

||| BinarySimulatedOp impolementation of abstract unitary application (that is, whatever one built using UStateT)
applyUSTBinSimulated : {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> QStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i  Qubit)
applyUSTBinSimulated ust = MkQST (applyUSTBin' ust )

baseStringFuncs: (n:Nat) -> String
baseStringFuncs n = ("import random\n" ++ "import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n")


baseStringVis : (n:Nat) -> String
baseStringVis n = ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n\n")
  

public export
RunUnitaryOp BinarySimulatedOp where
  supplyQubits = newQubitsBinSimulatedUST
  applyUStateT = applyUSTBinSimulatedSimOp
  runUnitaryOp = runUnitaryOpBinSimOp
  applyUStateTSplit = applyUSTBinSimulatedSplitSimOp

      --- Due to Idris2 not figuring out equivalences of power x 0 = 1 automatically, the below has to be done in a different way here.
-------------UnitaryMatrix implementation of UnitaryRun --------------

public export
UnitaryMatrix : Nat ->  Type
UnitaryMatrix n = Matrix (power 2 n) (power 2 n) 

public export
idU :{n:Nat} -> UnitaryMatrix n
idU {n} = matrixId (power 2 n)
  

private
newQubitsMatrix : (q : Nat) -> (1 _ : Matrix 1 1) -> (LPair (UnitaryMatrix (q)) (LVect q Qubit))
newQubitsMatrix q un =
    let (qubits # (v', newcounter))= newQubitsPointers q Z []
        in
          let (unFree , vac) = dupMatrixCD un in
            (rewrite multZeroLeftZero (power 2 q) in rewrite sym $ plusZeroRightNeutral (power 2 q) in (unFree `tensorProductAny` (idU {n = q}) )) # qubits



private
newQubitsMZ' : (q : Nat) -> (1 _ : Matrix 1 1) -> (LPair (UnitaryMatrix (q)) (LVect q Qubit))
newQubitsMZ' q un =
    let (qubits # (v', newcounter))= newQubitsPointers q Z []
        in
          let (unFree , vac) = dupMatrixCD un in
            (rewrite multZeroLeftZero (power 2 q) in rewrite sym $ plusZeroRightNeutral (power 2 q) in (unFree `tensorProductAny` (idU {n = q}) )) # qubits


|||This is a little annoying, but we have to force Idris2 to realize power 2 0 = 1 automatically, else buildUnitary 
||| does not complite for UnitaryMatrix
private
newQubitsUM' : {m:Nat} -> (q : Nat) -> (1 _ : UnitaryMatrix m) -> (LPair (UnitaryMatrix (m + q)) (LVect q Qubit))
newQubitsUM' {m = Z} q un =
    let (qubits # (v', newcounter))= newQubitsPointers q Z []
        in
          let (unFree , vac) = dupMatrixCD un in
            ( rewrite multPowerPowerPlus 2 Z q in (unFree `tensorProductAny` (idU {n = q}) )) # qubits
newQubitsUM' {m = S Z} q un =
    let (qubits # (v', newcounter))= newQubitsPointers q (S Z) (makeNeutralVect 1)
        in
          let (unFree , vac) = dupMatrixCD un in
            ( rewrite multPowerPowerPlus 2 (S Z) q in (unFree `tensorProductAny` (idU {n = q}) )) # qubits
newQubitsUM' {m = S k} q un =
    let (qubits # (v', newcounter))= newQubitsPointers q (S k) (makeNeutralVect (S k)) 
        in
          let (unFree , vac) = dupMatrixCD un in
            ( rewrite multPowerPowerPlus 2 (S k) q in (unFree `tensorProductAny` (idU {n = q}) )) # qubits

||| Supply qubits for UnitaryMatrix
private
newQubitsUMST : {n:Nat} -> (p : Nat) -> UStateT (UnitaryMatrix n) (UnitaryMatrix (n+p)) (LVect p Qubit)
newQubitsUMST {n} p = MkUST (newQubitsUM' {m = n} p)

            --multPowerPowerPlus : (base, exp, exp' : Nat) -> power base (exp + exp') = (power base exp) * (power base exp')
||| Helper for Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUMSTR': {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect i Qubit))      
                   -> (1 _ : UnitaryMatrix n) -> LPair (UnitaryMatrix n) (LVect i Qubit)
applyUMSTR' ust un = 
  let (uOut # lvect) = runUStateT (idU) ust in
    let (uOutFree, vac) = dupMatrixCD uOut in --These are helpful because then a linear matrix multiplication does not have to be defined.
      let (unFree, vac) = dupMatrixCD un in
        let unew = uOutFree `matrixMult` unFree in
          do unew # (lvect)

||| UnitaryMatrix implementation of abstract UnitaryMatrix application (that is, whatever one built using UStateT)
applyUMSTSimulatedR : {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect i Qubit))      
                   -> UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect i  Qubit)
applyUMSTSimulatedR ust = MkUST (applyUMSTR' ust )

||| Helper for UnitaryMatrix implementation of abstract UnitaryMatrix application (that is, whatever one built using UStateT)
applyUMSTSplit': {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> (1 _ : UnitaryMatrix n) -> LPair (UnitaryMatrix n) (LVect (i + j) Qubit)
applyUMSTSplit' ust un = 
  let (uOut # (lvi # lvj)) = runUStateT idU ust in
    let (uOutFree, vac) = dupMatrixCD uOut in
      let (unFree, vac) = dupMatrixCD un in
        let unew = uOutFree `matrixMult` unFree in
          do unew # (lvi ++ lvj)

||| UnitaryMatrix implementation of abstract UnitaryMatrix application (that is, whatever one built using UStateT)
applyUMSTSimulatedSplit : {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LPair (LVect i Qubit) (LVect j Qubit)))      
                   -> UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect (i + j) Qubit)
applyUMSTSimulatedSplit ust = MkUST (applyUMSTSplit' ust )


runUnitaryMatrixOp' : {n:Nat} -> UStateT (UnitaryMatrix 0) (UnitaryMatrix n) (LVect n Qubit) -> (UnitaryMatrix n)
runUnitaryMatrixOp' ust = let un # lv = runUStateT (idU {n = Z}) ust in
                      let () = discardq lv in
                        un
power2one : (power 2 1) = 2
power2one = Refl

power2OneMore : {m:Nat} -> mult (power 2 m) (power 2 1) = (power 2 (m+1))
power2OneMore  = rewrite multPowerPowerPlus 2 m 1 in rewrite power2one in Refl

||| this needs to be made explicit, for whatever reason, due to idris not finding the right place to apply commtativity
multCommPower2 : {m:Nat} -> mult (power 2 m) 2 = mult 2 (power 2 m) 
multCommPower2 {m} = multCommutative (power 2 m) 2

powerPlusIsMult : {m:Nat} ->  plus (power 2 m) (power 2 m) = mult (power 2 m) (power 2 1) 
powerPlusIsMult {m} = rewrite powerOneNeutral 2 in rewrite multCommPower2 {m = m} in rewrite multZeroLeftZero (power 2 m) in rewrite plusZeroRightNeutral (power 2 m) in Refl

||| Prepare a single new qubitt; this is necessary to define separately due to Idris not being able to figure out some type equalities die to the use of powers
supplyQubitM : {n:Nat} -> UStateT (Matrix (power 2 n) (power 2 n)) (UnitaryMatrix (S n)) Qubit
supplyQubitM = MkUST (newQubit') where
  newQubit' : {m:Nat} -> (1 _ : Matrix (power 2 m) (power 2 m)) -> (LPair (UnitaryMatrix (S m)) (Qubit))
  newQubit' {m = Z} un =
    let ([qubit] # (v', newcounter))= newQubitsPointers 1 Z [] 
        in
          let (unFree , vac) = dupMatrixCD un in
            (rewrite plusZeroRightNeutral (power 2 Z) in rewrite powerPlusIsMult {m = Z} in (unFree `tensorProductAny` (idU {n = 1}) )) # qubit

  newQubit' {m = S k} un =
    let ([qubit] # (v', newcounter))= newQubitsPointers 1 (S k) (makeNeutralVect (S k)) 
        in
          let (unFree , vac) = dupMatrixCD un in
            (rewrite plusZeroRightNeutral (power 2 (S k)) in rewrite powerPlusIsMult {m = (S k)} in (unFree `tensorProductAny` (idU {n = 1}) )) # qubit


public export
RunUnitaryOp UnitaryMatrix where
  supplyQubits = newQubitsUMST
  supplyQubit = supplyQubitM
  applyUStateT = applyUMSTSimulatedR
  runUnitaryOp = runUnitaryMatrixOp'
  applyUStateTSplit = applyUMSTSimulatedSplit

--- Due to the smae thng as above, Idris2 not figuring out equivalences of power x 0 = 1 automatically, this has to be done in a different way here.

export
neutralRunM : {n:Nat} -> (1_ : UStateT (UnitaryMatrix 0) (UnitaryMatrix n) (LVect n Qubit)) -> UnitaryMatrix n
neutralRunM ust = let op # lvect = runUStateT (idU {n = Z}) ust in
                        let () = discardq lvect in
                          op                      

public export
exportUnitaryMatrixSelf : {i:Nat} -> (1_: UnitaryMatrix n) -> (1 _ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect i Qubit) ) -> (UnitaryMatrix n) 
exportUnitaryMatrixSelf un ust = let op # lvect = runUStateT un ust in
                                      let () = discardq lvect in
                                        op

export
buildUnitaryM: {n:Nat} -> ((1_ : LVect n Qubit) -> (UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect n Qubit))) 
                        -> (UnitaryMatrix n)
buildUnitaryM f = neutralRunM {n=n} (do
    qs <- supplyQubits {t = UnitaryMatrix } {n = 0} n
    qsOut <- applyUStateT {t = UnitaryMatrix } {n = n} (f qs)
    pure qsOut)
  
||| example of how to bypass RunUnitaryOp 
export
buildUnitaryMatrix': {n:Nat} -> ((1_ : LVect n Qubit) -> (UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect n Qubit))) -> UnitaryMatrix n
buildUnitaryMatrix' {n} f = let un # qs = newQubitsMZ' n (idU {n = Z}) in
  exportUnitaryMatrixSelf (idU) (f qs)    

---------------------- for generalized wauntum data ------------------------

private
newQuditsUM' :
  {base : Nat} -> {m : Nat} ->
  (q : Nat) ->
  (1 _ : QuditUM base m) ->
  LPair (QuditUM base (m + q)) (LVect q Qubit)
newQuditsUM' {base} {m} q un =
  let (wires # (v', newcounter)) = newQubitsPointers q m (makeNeutralVect m) in
  let (unFree, vac) = dupMatrixCD un in
  let grown : Matrix (power base (m + q)) (power base (m + q)) =
        rewrite multPowerPowerPlus base m q in
          (unFree `tensorProductAny` (idQU {base} {n = q}))
  in grown # wires

private
newQuditsUMST :
  {base : Nat} -> {n : Nat} ->
  (p : Nat) ->
  UStateT (QuditUM base n) (QuditUM base (n + p)) (LVect p Qubit)
newQuditsUMST {base} {n} p = MkUST (newQuditsUM' {base} {m = n} p)

applyUMSTR_Qudit' :
  {base : Nat} -> {n : Nat} -> {i : Nat} ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LVect i Qubit)) ->
  (1 _ : QuditUM base n) ->
  LPair (QuditUM base n) (LVect i Qubit)
applyUMSTR_Qudit' {base} {n} ust un =
  let (uOut # lvect) = runUStateT (idQU {base} {n}) ust in
  let (uOutFree, vac1) = dupMatrixCD uOut in
  let (unFree,  vac2)  = dupMatrixCD un in
  let unew = uOutFree `matrixMult` unFree in
    unew # lvect

public export
applyUMSTSimulatedR_Qudit :
  {base : Nat} -> {n : Nat} -> {i : Nat} ->
  (1 _ : UStateT (QuditUM base n) (QuditUM base n) (LVect i Qubit)) ->
  UStateT (QuditUM base n) (QuditUM base n) (LVect i Qubit)
applyUMSTSimulatedR_Qudit ust = MkUST (applyUMSTR_Qudit' ust)

public export
neutralRunQuditUM :
  {base : Nat} -> {n : Nat} ->
  (1 _ : UStateT (QuditUM base 0) (QuditUM base n) (LVect n Qubit)) ->
  QuditUM base n
neutralRunQuditUM {base} {n} ust =
  let op # lvect = runUStateT (idQU {base} {n = 0}) ust in
  let () = discardq lvect in
    op

public export
buildQuditUM :
  {base : Nat} -> {n : Nat} ->
  ((1 _ : LVect n Qubit) -> UStateT (QuditUM base n) (QuditUM base n) (LVect n Qubit)) ->
  QuditUM base n
buildQuditUM {base} {n} f =
  neutralRunQuditUM {base} {n} (do
    qs    <- newQuditsUMST {base} {n = 0} n
    qsOut <- applyUMSTSimulatedR_Qudit {base} {n} (f qs)
    pure qsOut)

-------------Other Utilities--------------
export
reCalculateNew : {n:Nat} -> (v: Vect n Nat) -> Nat
reCalculateNew [] = 0
reCalculateNew {n = S k} (x::xs) = smallestMissing (sort ((x::xs)))

export
newVectOrder : {i:Nat} -> (p : Nat) -> (v: Vect i Nat) -> (Vect p Nat)
newVectOrder 0 _ = (([]))
newVectOrder {i} (S p) xs = let newcounter = (reCalculateNew (xs)) in
                let (v) = newVectOrder p (newcounter :: xs)
                  in ((newcounter :: v))

export
plusminusisN : (i,n:Nat) -> Vect (plus i (minus n i)) Nat -> Vect (plus (minus n i) i) Nat
plusminusisN i n vect = rewrite sym $ plusCommutative i (minus n i) in vect
 
export
plusminusn : (i,n:Nat) -> LTE i n -> Vect (plus (minus n i) i) Nat -> Vect n Nat
plusminusn i n lte vect = rewrite sym $ plusMinusLte i n lte in vect

export
newVectOrderN : {i:Nat} -> (n:Nat) -> (v: Vect i Nat) -> (Vect n Nat)
newVectOrderN n [] = newVectOrder n []
newVectOrderN {i} n v = case isLTE i n of
    Yes prfYes => let vect = (v ++ newVectOrder (minus n i) v) in 
                    let vectOut = (plusminusn i n prfYes (rewrite plusCommutative (minus n i) i in vect))
                      in vectOut
    No prf => toVectN $ makeNeutralVect n -- irrelevant in terms of control flow

export
findInLin : {n:Nat} -> (q : Nat) -> Vect (S n) Nat -> (Vect n Nat)
findInLin ( q) [] impossible
findInLin {n = Z} ( q) ( m :: xs) = []
findInLin {n = S r} ( q) ( m :: xs) = case decEq q m of
  Yes _ => xs
  No _ => ( m :: (findInLin {n = r} ( q) xs))
findInLin ( a) (x :: xs) = xs 

export
maximumControls: (n:Nat) -> (1_ : Vect i Nat) -> List Nat
maximumControls n [] = []
maximumControls n (k::ks) = case isLTE n k of
  Yes prf => k :: (maximumControls n ks)
  No prf => (maximumControls n ks)

