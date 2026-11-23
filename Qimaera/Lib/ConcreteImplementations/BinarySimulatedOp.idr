module Qimaera.Lib.ConcreteImplementations.BinarySimulatedOp
import Data.Vect
import Data.Vect.Sort
import Data.Nat
import Data.Nat.Views
import Decidable.Equality
import System.File
import Utilities.Injection
import Utilities.Matrix
import Utilities.Complex
import System.Random
import Utilities.Lemmas
import Qimaera.Lib.QStateT
import Control.Linear.LIO
import Utilities.LinearTypes
import Utilities.UnitaryLinear
import Qimaera.Lib.UStateT
import Control.Linear.LIO
import Qimaera.Lib.QuantumOp
import Qimaera.Lib.ConcreteImplementations.SimulatedOp
||| THIS MODULE IS UNDER REDEVELOPMENT (FOR PARSING OF OUTPUTS)
||| BE ADVISED!

  
||| add a string that describes a new function to string
addStringFunc: {n : Nat} -> String -> (counter:Nat) -> Vect n Qubit -> Unitary n -> String
addStringFunc str counter v g =
  let s = unitarytoQVisAt (toVectN v) g in
  let sOut = str ++ "\ndef Function"++ show counter++"(circuit):  \n" 
             ++ (s) ++
             "\treturn circuit\n\n" in
              sOut

||| Helper for BinarySimulatedOp impolementation of abstract unitary application (that is, whatever one built using UStateT)
applyUnitaryCirc': {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> (1 _ : BinarySimulatedOp n) -> R (LPair (BinarySimulatedOp n) (LVect i Qubit))
applyUnitaryCirc' ust (MkBinarySimulatedOp un v counter str) = 
  let ((MkBinarySimulatedOp unrun vnew vacuousCounter str) # lvect) = runUStateT (MkBinarySimulatedOp IdGate v counter str) ust in
      let strnew = addStringFunc str counter v unrun in
        let unew = compose unrun un in
          do pure1 ((MkBinarySimulatedOp unew vnew (S counter) strnew) # (lvect))

||| BinarySimulatedOp impolementation of abstract unitary application (that is, whatever one built using UStateT)
applyUnitaryCircSimulated : {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))      
                   -> QStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i  Qubit)
applyUnitaryCircSimulated ust = MkQST (applyUnitaryCirc' ust )

||| Helper for BinarySimulatedOp impolementation of abstract unitary application (that is, whatever one built using UStateT)
applyUDirectlyCirc': {n : Nat} -> {i : Nat} -> (Unitary i) -> (1_ : LVect i Qubit)
                   -> (1 _ : BinarySimulatedOp n) -> R (LPair (BinarySimulatedOp n) (LVect i Qubit))
applyUDirectlyCirc' {n} ui li (MkBinarySimulatedOp un v counter str) = 
      let lvect # vect = distributeDupedLVectVect li in
        let uibig # _ = (applySafe ui (IdGate{n = n}) (positions v vect)) in
          let strnew = addStringFunc str counter v uibig in
            let unew # _ = applySafe ui un (positions v vect) in
              do pure1 ((MkBinarySimulatedOp unew v (S counter) strnew) # (lvect))

||| BinarySimulatedOp impolementation of abstract unitary application (that is, whatever one built using UStateT)
applyUDirectlyCircSimulated : {n : Nat} -> {i : Nat} -> (Unitary i) -> (1_ : LVect i Qubit)      
                   -> QStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit)
applyUDirectlyCircSimulated ui li = MkQST (applyUDirectlyCirc' ui li)


||| add a string that describes all of the gates before measurement as one string
addStringFuncMeas: {n : Nat} -> String -> (counter:Nat) -> Vect n Qubit -> Unitary n -> String
addStringFuncMeas str counter v g =
  let s = unitarytoQVisAt (toVectN v) g in
    let sOut = str ++ "\ndef AllUnitariesBeforeFunc"++ show counter++"InOne(circuit):  \n" ++ (s) ++
             "\treturn circuit\n\n" in
              sOut

||| string that 
addFuncOfFuncs': (countUp:Nat) -> (counter:Nat) -> String
addFuncOfFuncs' Z Z = ""
addFuncOfFuncs' (S m) Z = ""
addFuncOfFuncs' Z (S k)= "\tFunction0(circuit)\n" ++ addFuncOfFuncs' (S Z) k
addFuncOfFuncs' (S m) (S k) = "\tFunction"++ show (S m)++"(circuit)\n" ++ addFuncOfFuncs' (S (S m)) k

||| string that 
addFuncOfFuncs: (counter:Nat) -> String
addFuncOfFuncs Z = ""
addFuncOfFuncs (S k) = addFuncOfFuncs' Z (S k)

||| Measurement for a simulated circuit; this is randomized 50%-50%;
||| This is precisely the intention of this implementation, to get the circuits produced
||| by algorithms, including variational ones, depending on measurement outcomes, randomly
private
measureCirc' : {n : Nat} -> (i : Nat) -> (wire : Nat) ->
           (1 _ : BinarySimulatedOp (S n)) ->
           R (LFstPair (BinarySimulatedOp n) (Bool))
measureCirc' {n} i wire (MkBinarySimulatedOp usn w counter str) = 
  let strOut = str ++ "\tcircuit.measure("++ show wire ++ ", "++ show wire ++")\n" in
    do
    let newQubits = removeElem w i
    randnb <- liftIO1 (rndFin 1)
    case randnb of 
      0 => do
        pure1 (MkBinarySimulatedOp IdGate newQubits (counter) strOut # (False))
      1 => do
        pure1 (MkBinarySimulatedOp IdGate newQubits (counter) strOut # (True))

||| a version for non/individual measurements       
private
measureCircNoStr' : {n : Nat} -> (i : Nat) ->
           (1 _ : BinarySimulatedOp (S n)) ->
           R (LFstPair (BinarySimulatedOp n) (Bool))
measureCircNoStr' {n} i (MkBinarySimulatedOp usn w counter str) = do
  let newQubits = removeElem w i
  randnb <- liftIO1 (rndFin 1)
  case randnb of 
     0 => do
       pure1 (MkBinarySimulatedOp IdGate newQubits (counter) str # (False))
     1 => do
       pure1 (MkBinarySimulatedOp IdGate newQubits (counter) str # (True))       

||| Relevant version of list index       
public export
listIndexCirc : (1 _ : BinarySimulatedOp n) -> (1 _ : Qubit) -> LFstPair (LPair (BinarySimulatedOp n) Qubit) Nat
listIndexCirc (MkBinarySimulatedOp us v counter str ) q = let q # k = qubitToNatPair q in (MkBinarySimulatedOp us v counter str # q) # (listIndexN v k)

measureQubitCirc'' : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) ->
                 (1 _ : BinarySimulatedOp (i + n)) -> R (LPair (BinarySimulatedOp n) ((Vect i Bool)))
measureQubitCirc'' [] qs = pure1 (qs # [])
measureQubitCirc'' (x :: xs) (MkBinarySimulatedOp uin v counter str) = 
    let (qs' # q) # y = listIndexCirc (MkBinarySimulatedOp uin v counter str) x in
      let q # k = qubitToNatPair q in
      let () = discardq [q] in   
      do  
        (s # (b)) <- measureCirc' y k qs'
        (s1 # (bs)) <- measureQubitCirc'' xs s
        case bs of 
            [] => pure1 (s1 # ([b]))
            (b' :: bs') => pure1 (s1 # ((b :: b' :: bs')))

private
measureQubitsCirc' : {n : Nat} -> {i : Nat} ->
                 (1 _ : LVect i Qubit) ->
                 (1 _ : BinarySimulatedOp (i + n)) -> R (LPair (BinarySimulatedOp n) ((Vect i Bool)))
measureQubitsCirc' [] qs = pure1 (qs # [])
measureQubitsCirc' (x :: xs) (MkBinarySimulatedOp uin v counter str) = 
  let newStr = (addStringFuncMeas str counter v uin) in
  let ((MkBinarySimulatedOp uin v counter strOut) # q) # y = listIndexCirc (MkBinarySimulatedOp uin v counter newStr) x in
    let q # k = qubitToNatPair q in
    let () = discardq [q] in 
      let sIn = strOut ++ "\ndef AllFunctionsBefore"++ show counter++"(circuit): \n" ++ (addFuncOfFuncs counter) 
                ++ "\treturn circuit\n\n" ++ "\ndef Function"++ show (counter)++"(circuit): \n" in 
      do  
        (s # (b)) <- measureCirc' y k (MkBinarySimulatedOp IdGate v (S counter) sIn) 
        ((MkBinarySimulatedOp idn v counter sOut) # (bs)) <- measureQubitCirc'' xs s
        case bs of 
            [] => let sFinal = sOut ++ "\treturn circuit\n\n" in pure1 ((MkBinarySimulatedOp idn v counter sFinal) # ([b]))
            (b' :: bs') =>let sFinal = sOut ++ "\treturn circuit\n\n" in pure1 ((MkBinarySimulatedOp idn v counter sFinal) # ((b :: b' :: bs')))

||| Because of having to structure the output files, we need separate measurtement functions, where we can have a single return statement.
measureAllCirc'' : {n : Nat} -> 
                 (1 _ : LVect n Qubit) ->
                 (1 _ : BinarySimulatedOp n) -> R (LPair (BinarySimulatedOp 0) ((Vect n Bool)))
measureAllCirc'' [] qs = pure1 (qs # [])
measureAllCirc'' (x :: xs) (MkBinarySimulatedOp uin v counter str) = 
    let (qs' # q) # y = listIndexCirc (MkBinarySimulatedOp uin v counter str) x in
      let () = discardq [q] in   
      do  
        (s # (b)) <- measureCircNoStr' y qs'
        (s1 # (bs)) <- measureAllCirc'' xs s
        case bs of 
            [] => pure1 (s1 # ([b]))
            (b' :: bs') => pure1 (s1 # ((b :: b' :: bs')))


measureAllCirc' : {n : Nat} -> 
                 (1 _ : LVect n Qubit) ->
                 (1 _ : BinarySimulatedOp n) -> R (LPair (BinarySimulatedOp 0) ((Vect n Bool)))
measureAllCirc' [] qs = pure1 (qs # [])
measureAllCirc' (x :: xs) (MkBinarySimulatedOp uin v counter str) = 
  let newStr = (addStringFuncMeas str counter v uin) in
  let ((MkBinarySimulatedOp uin v counter strOut) # q) # y = listIndexCirc (MkBinarySimulatedOp uin v counter newStr) x in
    let () = discardq [q] in 
      let sIn = strOut ++ "\ndef AllFunctionsBefore"++ show counter++"(circuit): \n" ++ (addFuncOfFuncs counter) ++ "\treturn circuit\n\n"
                ++ "\ndef Function"++ show counter++"(circuit): \n\tcircuit.measure_all()\n\treturn circuit\n\n" in 
      do  
        (s # (b)) <- measureCircNoStr' y (MkBinarySimulatedOp IdGate v (S counter) sIn) 
        (s1 # (bs)) <- measureAllCirc'' xs s
        case bs of 
            [] => pure1 (s1 # ([b]))
            (b' :: bs') => pure1 (s1 # ((b :: b' :: bs')))

export
measureQubitsSimulatedCirc : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> QStateT (BinarySimulatedOp (i+n)) (BinarySimulatedOp n) (Vect i Bool)
measureQubitsSimulatedCirc v = MkQST (measureQubitsCirc' v)


export
measureAllSimulatedCirc : {n : Nat} -> (1 _ : LVect n Qubit) -> QStateT (BinarySimulatedOp n) (BinarySimulatedOp 0) (Vect n Bool)
measureAllSimulatedCirc v = MkQST (measureAllCirc' v)

baseStringFuncs: (n:Nat) -> String
baseStringFuncs n = ("import random\n" ++ "import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n")


baseStringVis : (n:Nat) -> String
baseStringVis n = ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n\n")
  
finalString : (n:Nat) -> (counter:Nat) -> String -> (name:String) ->  String
finalString n c str name = (str ++ "def OutputCircuit(n):  \n" 
                    ++ "\tcircuit = QuantumCircuit(n, n)\n" 
                    ++ (addFuncOfFuncs c) ++ "\treturn circuit\n\n"
                    ++ "qc = OutputCircuit(" ++ show n ++ ")\n\n" 
                    ++ "print(qc)\n\n"
                    ++ "qc.draw(output=\"mpl\", filename=\""++ name ++".jpeg\")")

runSimulatedCircVis : {n:Nat} -> QStateT (BinarySimulatedOp 0) (BinarySimulatedOp 0) (Vect n Bool) -> IO (Vect n Bool)
runSimulatedCircVis {n} s = LIO.run (do
  ((MkBinarySimulatedOp un w c str) # v) <- runQStateT (MkBinarySimulatedOp IdGate [] 0 (baseStringVis n)) s
  nothing <- putStrLn "Please give a name to the file you wish to export the circuit to:  "
  name <- getLine
  uinout <- writeFile (name ++ ".py") (finalString n c str name)
  case v of 
                    [] => pure []
                    (x :: xs) => pure (x :: xs))

||| Depricated because Unsafe, but useful sometimes: Implementation of run for BinarySimulatedOp
private
runSimulatedCircU : {i:Nat} -> (1_: BinarySimulatedOp n) -> (1 _ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit) ) -> LPair (BinarySimulatedOp n) (LVect i Qubit)
runSimulatedCircU {i = i} simop ust = runUStateT simop ust

||| Export a unitary out of BinarySim
private
exportUnitary' : {i:Nat} -> (1_: BinarySimulatedOp n) -> (1 _ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit) ) -> Unitary n
exportUnitary' {i = i} simop ust = let (MkBinarySimulatedOp un vn counter str) # lvect = runUStateT simop ust in
                                      let () = discardq lvect in
                                          un

||| Implementation of runSplit BinarySimulatedOp
private
runSplitSimulatedCircU : {i:Nat} -> {j:Nat} -> (1_: BinarySimulatedOp n) -> (1 _ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))  
                -> LPair (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))
runSplitSimulatedCircU {i = i} simop ust = runUStateT simop ust

||| Helper for impolementation of  applyUnitary
applyUnitarySimulatedCirc' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( MkUnitary (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : BinarySimulatedOp n) -> (LPair (BinarySimulatedOp n) (LVect i Qubit))
applyUnitarySimulatedCirc' lvIn ui (MkBinarySimulatedOp un v counter str)= 
    let lvOut # vect = distributeDupedLVectVect lvIn in 
      let unew # _ = (UnitaryLinear.applySafe ui un (positions v vect)) in (MkBinarySimulatedOp (unew) v counter str) # (lvOut)

||| BinarySimulatedOp impolementation of applyUnitary
export
applyUnitarySimulatedCirc : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> Unitary i -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit)
applyUnitarySimulatedCirc lvect ui = mkUST (applyUnitarySimulatedCirc' lvect (ui))

||| Helper for BinarySimulatedOp impolementation of applyUnitaryOwn (using self-defined datatype for unitaries)
private
applyUnitaryOwnCirc' : {n : Nat} -> {i : Nat} -> (1 _ : BinarySimulatedOp i) -> (1 _ : LVect i Qubit) ->
   (1 _ : BinarySimulatedOp n) -> (LPair (BinarySimulatedOp n) (LVect i Qubit))
applyUnitaryOwnCirc' {n} {i} (MkBinarySimulatedOp ui vacuousV vacuousC vacuousStr) lvIn (MkBinarySimulatedOp un v counter str) = 
  let lvOut # vect = distributeDupedLVectVect lvIn in 
    let unew # _ = (UnitaryLinear.applySafe ui un (positions v vect)) in (MkBinarySimulatedOp (unew) v counter str) # (lvOut)

    
||| BinarySimulatedOp impolementation of applyUnitaryOwn (using self-defined datatype for unitaries)
export
applyUnitaryOwnSimulatedCirc : {n : Nat} -> {i : Nat} -> (1 _ :LVect i Qubit) -> 
  (1 _ : BinarySimulatedOp i) -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit)
applyUnitaryOwnSimulatedCirc {n} {i} qbits simop = mkUST (applyUnitaryOwnCirc' {n =n} {i = i} simop qbits)


||| Auxiliary functstrn for applying a circuit to some qubits
private
combineAbs' : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))) -> (1 _ : BinarySimulatedOp n) -> (LPair (BinarySimulatedOp n) (LVect (i +j) Qubit))
combineAbs' ust (MkBinarySimulatedOp us v counter str) = let (Builtin.(#) opOut (lvect #rvect)) = (runSplitSimulatedCircU (MkBinarySimulatedOp us v counter str) ust) in do
 (Builtin.(#) opOut (LinearTypes.(++) lvect rvect))
 
export
combineAbsSimulatedCirc : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : (UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)) ))-> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect (i+j) Qubit)
combineAbsSimulatedCirc q = mkUST (combineAbs' q)

--(1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair Qubit (LVect i Qubit))) ->

--(1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair Qubit (LVect i Qubit))) ->

private
applyControlSimulated': {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1 _ : LVect i Qubit) -> (1 ownUnitary : BinarySimulatedOp i) ->        
    (1_ : BinarySimulatedOp (S n)) -> LPair (BinarySimulatedOp (S n)) (LVect (S i) Qubit)
applyControlSimulated' {n} c ts (MkBinarySimulatedOp ui vecuousV vacuousC vacuousStr) (MkBinarySimulatedOp usn vsn csn str)= 
    let c # k = qubitToNatPair c in
      let lvOut # targets = distributeDupedLVectVect ts in 
        let usnOut # _ = (applySafe (controlled ui) usn (positions vsn (k::targets))) in
          (MkBinarySimulatedOp usnOut vsn csn str)  # (c :: lvOut)

export
applyControlAbsSimulatedCirc: {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1 _ : LVect i Qubit) -> (1 ownUnitary : BinarySimulatedOp i) ->      
    UStateT (BinarySimulatedOp (S n)) (BinarySimulatedOp (S n)) (LVect (S i) Qubit)
applyControlAbsSimulatedCirc c ts ust = mkUST (applyControlSimulated' c ts ust)   


invertBinarySimulatedOp : (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit)) -> (1_ : (BinarySimulatedOp n)) -> LPair (BinarySimulatedOp n) (LVect i Qubit)
invertBinarySimulatedOp ust (MkBinarySimulatedOp u v counter str)=  
    let (MkBinarySimulatedOp un vn counter str) # lvOut = runUStateT (MkBinarySimulatedOp (IdGate {n = n}) v counter str) ust in
        let invu = adjoint un in
          let unew = compose invu u in
              (MkBinarySimulatedOp unew v counter str) # (lvOut)
export
adjointUSTSimCirc' : {n:Nat} ->(1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit)) -> (UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))
adjointUSTSimCirc' ust = mkUST (invertBinarySimulatedOp ust)



applyWithSplitLVects' : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> (1_: BinarySimulatedOp n) -> LPair (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVects' ust (MkBinarySimulatedOp un v counter str) = 
  let ((MkBinarySimulatedOp unew vnew vacuousCounter vacuousStr) # lvect) = runUStateT (MkBinarySimulatedOp un v counter str) ust in
        let unew = compose unew un in
          do ((MkBinarySimulatedOp unew vnew counter str) # (lvect))

||| Implementation of abstract split application - representatstrnally useful
applyWithSplitLVectsSimulatedCirc : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVectsSimulatedCirc ust = mkUST (applyWithSplitLVects' ust)

applyParallelSimulatedBinary': {n : Nat} -> {i : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit))     
                   -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect j Qubit))   
                   -> (1 _ : BinarySimulatedOp n) -> LPair (BinarySimulatedOp n) (LVect (i + j) Qubit)
applyParallelSimulatedBinary' ust1 ust2 (MkBinarySimulatedOp un vn cn st) = 
  let ((MkBinarySimulatedOp unew1 vnew1 vacnew1 vacstr1) # lvecti) = runUStateT (MkBinarySimulatedOp IdGate vn cn st) ust1 in -- there are multiple choices for what order to do what in, this is one correct one
    let ((MkBinarySimulatedOp unew2 vnew2 vacnew2 vacstr2) # lvectj) = runUStateT (MkBinarySimulatedOp IdGate vn cn st) ust2 in
        let unewest = compose unew1 un in
          let uOut = compose unew2 unewest in
            do ((MkBinarySimulatedOp uOut vnew2 cn st) # (lvecti ++ lvectj))

export
applyParallelSimulatedBinary: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) ((LVect i Qubit)))
                        -> (1_ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) ((LVect j Qubit))) -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect (i + j) Qubit)
applyParallelSimulatedBinary ust1 ust2 = mkUST (applyParallelSimulatedBinary' ust1 ust2)

||| Depricated because Unsafe (but can be useful) -- Implementation of exporting self out of SimulatedOp
private
exportSelf' : {i:Nat} -> (1_: BinarySimulatedOp n) -> (1 _ : UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect i Qubit) ) -> BinarySimulatedOp n
exportSelf' {i = i} simop ust = let op # lvect = runUStateT simop ust in
                                      let () = discardq lvect in
                                          op

private
applyMControlSimulated': {n : Nat} -> {i : Nat} -> {k : Nat} -> (1_ : LVect (S k) Qubit) -> (1_ : LVect i Qubit) -> (1_ :  BinarySimulatedOp i) ->
    (1_ : BinarySimulatedOp ( (S k) + n )) -> LPair ( BinarySimulatedOp ((S k) + n)) (LVect ((S k) + i) Qubit)
applyMControlSimulated' {n} {i} [] ts ui usn impossible
applyMControlSimulated' {n} {i} {k = k} (c::cs) ts (MkBinarySimulatedOp ui vacuousV vacuousC vacuousStr) (MkBinarySimulatedOp usn vsn count str) = 
  let lvControls # controls = distributeDupedLVectVect (c::cs) in 
    let lvOut # targets = distributeDupedLVectVect ts in 
      let usnOut # _ = (applySafe (multipleControlled (S k) ui) usn (positions vsn (controls ++ targets))) in
        (MkBinarySimulatedOp usnOut vsn count str) # (lvControls ++ lvOut)

export
applyMControlBinarySimulatedOp: {n : Nat} -> {i : Nat} -> {k : Nat} -> (1_ : LVect (S k) Qubit) -> (1_ : LVect i Qubit) -> (1_ :  BinarySimulatedOp i) ->      
    UStateT (BinarySimulatedOp ((S k) + n)) (BinarySimulatedOp ((S k) +  n)) (LVect ((S k) +  i) Qubit)
applyMControlBinarySimulatedOp cs ts ui = mkUST (applyMControlSimulated' cs ts ui)   

||| implementation of parsion from a neutral element
private
neutralRun : {n:Nat} -> (1_ : UStateT (BinarySimulatedOp 0) (BinarySimulatedOp n) (LVect n Qubit)) -> BinarySimulatedOp n
neutralRun ust = let op # lvect = runUStateT (MkBinarySimulatedOp (IdGate {n = 0}) [] 0 "") ust in
                        let () = discardq lvect in
                          op 

|||implementaiton of build.
export
buildUnitary': {n:Nat} -> ((1_ : LVect n Qubit) -> (UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect n Qubit))) -> BinarySimulatedOp n
buildUnitary' {n} f = neutralRun (do
  qs <- supplyQubits n
  qsOut <- applyUStateT (f qs)
  pure qsOut)

||| helper for general controlling operation over  UStateT
controlMUST': {n : Nat} -> {i : Nat} -> {j : Nat} ->(1 controls : LVect i Qubit) -> (1 locations : LVect j Qubit) ->
                   (targetPattern : ((1_ :LVect j Qubit) -> UStateT (BinarySimulatedOp j) (BinarySimulatedOp j) (LVect j Qubit)))
                   -> (1_: BinarySimulatedOp n) -> LPair  (BinarySimulatedOp n) (LVect (i + j) Qubit)
controlMUST' {n} {i} {j} ctrl locs targetP  (MkBinarySimulatedOp un vn counter str) = let (MkBinarySimulatedOp u vacvn vaccounter vacstr) = buildUnitary' {n = j} targetP in
  let lvControls # controls = distributeDupedLVectVect ctrl in 
  let qs # targets = distributeDupedLVectVect locs in
    let uc = multipleControlled i u in
      let unOut # _ = (applySafe uc un (positions vn (controls ++ targets))) in
        (MkBinarySimulatedOp unOut vn counter str) # (lvControls ++ qs)

||| Implementation of general controlling operation over  UStateT
controlMUSTSimOp:  {n : Nat} -> {i : Nat} -> {j : Nat} ->(1 controls : LVect i Qubit) -> (1 locations : LVect j Qubit) ->
                   (targetPattern : ((1_ :LVect j Qubit) -> UStateT (BinarySimulatedOp j) (BinarySimulatedOp j) (LVect j Qubit)))
                   -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect (i + j) Qubit)
controlMUSTSimOp ctrl loc targetP = mkUST (controlMUST' ctrl loc targetP)

||| helper for general controlling operation over  UStateT
controlUST': {n : Nat} -> {i : Nat} -> (1 control : Qubit) -> (1 locations : LVect i Qubit) ->
                   (targetPattern : ((1_ :LVect i Qubit) -> UStateT (BinarySimulatedOp i) (BinarySimulatedOp i) (LVect i Qubit)))
                   -> (1_ :BinarySimulatedOp n) -> LPair (BinarySimulatedOp n) (LVect (S i) Qubit)
controlUST' {n} {i} ctrl locs targetP  (MkBinarySimulatedOp un vn counter str) = let (MkBinarySimulatedOp u vacvn vaccounter vacstr) = buildUnitary' {n = i} targetP in
  let q # c = qubitToNatPair ctrl in
  let qs # ts= distributeDupedLVectVect locs in
    let uc = controlled u in
      let unOut # _ = (applySafe uc un (positions vn (c::ts))) in
        (MkBinarySimulatedOp unOut vn counter str) # (q::qs)

||| implementation of control - not necessary, default does it.
controlUSTBinSimOp: {n : Nat} -> {i : Nat} -> (1 control : Qubit) -> (1 locations : LVect i Qubit) ->
                   (targetPattern : ((1_ :LVect i Qubit) -> UStateT (BinarySimulatedOp i) (BinarySimulatedOp i) (LVect i Qubit)))
                   -> UStateT (BinarySimulatedOp n) (BinarySimulatedOp n) (LVect (S i) Qubit)
controlUSTBinSimOp ctrl loc targetP = mkUST (controlUST' ctrl loc targetP)


export
UnitaryOp BinarySimulatedOp where
  applyUnitary = applyUnitarySimulatedCirc
  applyUnitaryOwn = applyUnitaryOwnSimulatedCirc
  applyControlledOwn = applyControlAbsSimulatedCirc
  applyMultipleControlledOwn = applyMControlBinarySimulatedOp
  adjointUST = adjointUSTSimCirc'
  applyParallel = applyParallelSimulatedBinary
  combineAbs= combineAbsSimulatedCirc
  buildUnitary = buildUnitary'
  controlUST = controlUSTBinSimOp
  multipleControlUST = controlMUSTSimOp

export
QuantumOp BinarySimulatedOp where
  newQubits    = newQubitsSimulatedCirc
  applyUST = applyUnitaryCircSimulated
  applyUnitaryDirectly = applyUDirectlyCircSimulated
  measure      = measureQubitsSimulatedCirc
  measureAll = measureAllSimulatedCirc
  run       = runSimulatedCircVis

