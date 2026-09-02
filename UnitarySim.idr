module UnitarySim

import Data.Vect
import Data.Nat
import Data.Vect.Sort
import Decidable.Equality
import Injection
import Lemmas
import UnitaryLinear
import UStateT
import LinearTypes
import QStateT
import QuantumOp


public export
runUnitarySim : {i:Nat} -> (1_: Unitary n) -> (1 _ : UStateT (Unitary n) (Unitary n) (LVect i Qubit) ) -> LPair (Unitary n) (LVect i Qubit)
runUnitarySim {i = i} un ust = runUStateT un ust

public export
runSplitUnitarySim : {i:Nat} -> {j:Nat} -> (1_: Unitary n) -> (1 _ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))  
                -> LPair (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit))
runSplitUnitarySim {i = i} un ust = runUStateT un ust

public export
exportUnitarySelf : {i:Nat} -> (1_: Unitary n) -> (1 _ : UStateT (Unitary n) (Unitary n) (LVect i Qubit) ) -> (Unitary n) 
exportUnitarySelf un ust = let op # lvect = runUStateT un ust in
                                      let () = discardq lvect in
                                        op

||| Auxiliary function for applying a circuit to some qubits
||| this has to recognize and handle the case where it is applied within an abstract control
||| since this is the only was it can receive an lvect of qubits that contains an unexpected element, this is easy to handle 
||| using decidability.
private
applyUnitary' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : Unitary n) -> (LPair (Unitary n) (LVect i Qubit))
applyUnitary' {n} {i} lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in 
                                      let unew # _ = (UnitaryLinear.applySafe ui u vect) in unew # (lvOut)
           
export
applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (Unitary n) (Unitary n) (LVect i Qubit)
applyUnitarySimulated lvect ui = MkUST (applyUnitary' lvect (ui))


private
applyControlSimulated': {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : LVect i Qubit) -> (1_ : Unitary i) ->
    (1_ : Unitary (S n)) -> LPair (Unitary (S n)) (LVect (S i) Qubit)
applyControlSimulated' {n} {i} c ts ui usn = 
  let (c, k) = qubitToNatPair c in
    let lvOut # targets = distributeDupedLVectVect ts in 
      let usnOut # _ = (applySafe (controlled ui) usn (k::targets)) in
        usnOut # (c :: lvOut)

export
applyControlAbsSimulated: {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : LVect i Qubit) -> (1_ : Unitary i) ->      
    UStateT (Unitary (S n)) (Unitary (S n)) (LVect (S i) Qubit)
applyControlAbsSimulated c ts ui = MkUST (applyControlSimulated' c ts ui)   

export
explicitCombineL: (1_ : LVect (S k) Qubit) -> (1_ : LVect i Qubit) -> (LVect ((S k) + i) Qubit)
explicitCombineL lvL lvR = LinearTypes.(++) lvL lvR

explicitCombine: (Vect (S k) Nat) -> (Vect i Nat) -> (Vect ((S k) + i) Nat)
explicitCombine vL vR = (++) vL vR

private
applyMControlSimulated': {n : Nat} -> {i : Nat} -> {k : Nat} -> (1_ : LVect (S k) Qubit) -> (1_ : LVect i Qubit) -> (1_ : Unitary i) ->
    (1_ : Unitary ( (S k) + n )) -> LPair (Unitary ((S k) + n)) (LVect ((S k) + i) Qubit)
applyMControlSimulated' {n} {i} [] ts ui usn impossible
applyMControlSimulated' {n} {i} {k = k} (c::cs) ts ui usn = 
  let lvControls # controls = distributeDupedLVectVect (c::cs) in 
    let lvOut # targets = distributeDupedLVectVect ts in 
      let usnOut # _ = (applySafe (multipleControlled (S k) ui) usn (explicitCombine controls targets)) in
        usnOut # (lvControls ++ lvOut)

export
applyMControlAbsSimulated: {n : Nat} -> {i : Nat} -> {k : Nat} -> (1_ : LVect (S k) Qubit) -> (1_ : LVect i Qubit) -> (1_ : Unitary i) ->      
    UStateT (Unitary ((S k) + n)) (Unitary ((S k) +  n)) (LVect ((S k) +  i) Qubit)
applyMControlAbsSimulated cs ts ui = MkUST (applyMControlSimulated' cs ts ui)   


export
duplicateLinU: (1_ : Unitary n) -> Pair (Unitary n) (Unitary n)
duplicateLinU IdGate = (IdGate, IdGate)
duplicateLinU (H j g {prf} ) = let (g1,g2) = duplicateLinU g in ((H j g1 {prf = prf}), (H j g2 {prf = prf}))
duplicateLinU (P p j g {prf}) = let (g1,g2) = duplicateLinU g in ((P p j g1 {prf = prf}), (P p j g2 {prf = prf}))
duplicateLinU (CNOT c t g {prf1} {prf2} {prf3 = prf3}) = let (g1,g2) = duplicateLinU g in ((CNOT c t g1 {prf1 = prf1} {prf2 = prf2} {prf3 = prf3}), (CNOT c t g2 {prf1 = prf1} {prf2 = prf2} {prf3 = prf3}))

||| Helper for Unitary implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUnitaryAbs': {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))      
                   -> (1 _ : Unitary n) -> LPair (Unitary n) (LVect i Qubit)
applyUnitaryAbs' ust un = 
  let (unew # lvect) = runUStateT IdGate ust in
        let ufinal = compose unew un in
          do ufinal # (lvect)

||| Unitary implementation of abstract unitary application (that is, whatever one built using UStateT) 
applyUnitaryAbsSimulated : {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))      
                   -> UStateT (Unitary n) (Unitary n) (LVect i  Qubit)
applyUnitaryAbsSimulated ust = MkUST (applyUnitaryAbs' ust )


applyWithSplitLVects' : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> (1_: Unitary n) -> LPair (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVects' ust (un) = 
    let ((unew) # lvect) = runUStateT IdGate ust in
        let unew = compose unew un in
          do ((unew) # (lvect))

||| Implementation of abstract split application - representationally useful
applyWithSplitLVectsSimulated : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVectsSimulated ust = MkUST (applyWithSplitLVects' ust)

||| Helper for implementation of abstract controlled split application 
applyControlledUSplitSim' : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : LVect i Qubit) -> (1_ : LVect j Qubit) -> (1_ : Unitary (i + j))
                             -> (1_ : Unitary (S n)) -> LPair (Unitary (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledUSplitSim' c tsi tsj uij usn= 
  let (c, k) = qubitToNatPair c in
    let lvMid # targets = distributeDupedLVectVect (tsi ++ tsj) in
      let lvOutL # lvOutR = splitLVinto i j lvMid in
        let usnOut # _ = (applySafe (controlled uij) usn (k::targets)) in
          usnOut # (c :: lvOutL # lvOutR)

||| Implementation of abstract controlled split application     
applyControlledSimulatedSplit: {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : LVect i Qubit) -> (1_ : LVect j Qubit) -> (1_ : Unitary (i + j))
                             -> UStateT (Unitary (S n)) (Unitary (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledSimulatedSplit c tsi tsj uij = MkUST $ applyControlledUSplitSim' c tsi tsj uij


private
combineAbs' : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit))) -> (1 _ : Unitary n) -> (LPair (Unitary n) (LVect (i +j) Qubit))
combineAbs' ust (ui) = let (Builtin.(#) opOut (lvect #rvect)) = (runSplitUnitarySim ( ui) ust) in do
 (Builtin.(#) opOut (LinearTypes.(++) lvect rvect))

 
export
combineAbsUnitarySimulated : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : (UStateT (Unitary n) (Unitary n) (LPair (LVect i Qubit) (LVect j Qubit)) ))-> UStateT (Unitary n) (Unitary n) (LVect (i+j) Qubit)
combineAbsUnitarySimulated q = MkUST (combineAbs' q)

applyParallelSimulated': {n : Nat} -> {i : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit))     
                   -> (1_ : UStateT (Unitary n) (Unitary n) (LVect j Qubit))   
                   -> (1 _ : Unitary n) -> LPair (Unitary n) (LVect (i + j) Qubit)
applyParallelSimulated' ust1 ust2 un = 
  let (unew1# lvecti) = runUStateT IdGate ust1 in -- there are multiple choices for what order to do what in, this is one correct one
    let (unew2 # lvectj) = runUStateT IdGate ust2 in
        let unewest = compose unew1 un in
          let uOut = compose unew2 unewest in
            do (uOut # (lvecti ++ lvectj))

applyParallelSimulated: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (Unitary n) (Unitary n) ((LVect i Qubit)))
                        -> (1_ : UStateT (Unitary n) (Unitary n) ((LVect j Qubit))) -> UStateT (Unitary n) (Unitary n) (LVect (i + j) Qubit)
applyParallelSimulated ust1 ust2 = MkUST (applyParallelSimulated' ust1 ust2)


private
applyUnitaryOwn' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> (1_ : Unitary i) -> (1 _ : Unitary n) -> (LPair (Unitary n) (LVect i Qubit))
applyUnitaryOwn' lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in 
                                let unew # _ = (UnitaryLinear.applySafe ui u vect) in unew # (lvOut)
           
export
applyUnitaryOwnSimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> (1_ : Unitary i) -> UStateT (Unitary n) (Unitary n) (LVect i Qubit)
applyUnitaryOwnSimulated lvect ui = MkUST (applyUnitaryOwn' lvect (ui))

applyInternal : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (Unitary n) (Unitary n) (LVect i Qubit)
applyInternal lvect ui = MkUST (applyUnitary' lvect ui)

export
applyHSim : {n : Nat} -> (1 _ : Qubit) -> UStateT (Unitary n) (Unitary n) (LVect 1 Qubit)
applyHSim q = do
    [q1] <- applyInternal {n} {i = 1} [q] (UnitaryLinear.HGate)
    pure [q1]

export
applyPSim : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (Unitary n) (Unitary n) (LVect 1 Qubit)
applyPSim p q = do
    [q1] <- applyInternal {n} {i = 1} [q] (UnitaryLinear.PGate p)
    pure [q1]

export
applyCNOTSim : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (Unitary n) (Unitary n) (LVect 2 Qubit)
applyCNOTSim q1 q2 = do
    [q1,q2] <- applyInternal {n} {i = 2} (q1::[q2]) UnitaryLinear.CNOTGate
    pure (q1::q2::[])

invert: (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit)) -> (1_ : (Unitary n)) -> LPair (Unitary n) (LVect i Qubit)
invert ust un =  
    let unOut # lvOut = runUStateT IdGate ust in
      let (invFree, invDunny) = duplicateLinU unOut in
        let invu = adjoint invFree in
          let (unFree, unDunny) = duplicateLinU un in
            let unew = compose invu unFree in
              unew # (lvOut)
 
export
adjointUST' : {n:Nat} -> (1_ : UStateT (Unitary n) (Unitary n) (LVect i Qubit)) -> (UStateT (Unitary n) (Unitary n) (LVect i Qubit))
adjointUST' ust = MkUST (invert ust)  


export
neutralRun' : {n:Nat} -> (1_ : UStateT (Unitary 0) (Unitary n) (LVect n Qubit)) -> Unitary n
neutralRun' ust = let op # lvect = runUStateT (IdGate {n = 0}) ust in
                        let () = discardq lvect in
                          op 

export
buildUnitary': {n:Nat} -> ((1_ : LVect n Qubit) -> (UStateT (Unitary n) (Unitary n) (LVect n Qubit))) -> Unitary n
buildUnitary' {n} f = neutralRun' (do
  qs <- supplyQubits n
  qsOut <- applyUStateT (f qs)
  pure qsOut)

export
withComputed: {n:Nat} -> {i:Nat} -> (1_ : LVect i Qubit) -> (1 g : Unitary i) ->  (1 f : Unitary i) -> (UStateT (Unitary n) (Unitary n) (LVect i Qubit)) 
withComputed {n} {i} qs uig uif =
  let (uig1, uig2) = duplicateLinU uig in
  let (uif1, vac) = duplicateLinU uif in
  let uigadj = adjoint uig2 in
  let full = uigadj . (uif1 . uig1) in
    applyUnitarySimulated qs full 

controlUST': {n : Nat} -> {i : Nat} -> (1 control : Qubit) -> (1 locations : LVect i Qubit) ->
                   (targetPattern : ((1_ :LVect i Qubit) -> UStateT (Unitary i) (Unitary i) (LVect i Qubit)))
                   -> (1_ :Unitary n) -> LPair (Unitary n) (LVect (S i) Qubit)
controlUST' {n} {i} ctrl locs targetP un = let u = buildUnitary' {n = i} targetP in -- this is handy because we already have it, but it is NOT needed to define thisß
  let (q, c) = qubitToNatPair ctrl in
  let qs # ts= distributeDupedLVectVect locs in
    let uc = controlled u in
      let unOut # _ = (applySafe uc un (c::ts)) in
        unOut # (q::qs)


controlUSTUnitary: {n : Nat} -> {i : Nat} -> (1 control : Qubit) -> (1 locations : LVect i Qubit) ->
                   (targetPattern : ((1_ :LVect i Qubit) -> UStateT (Unitary i) (Unitary i) (LVect i Qubit)))
                   -> UStateT (Unitary n) (Unitary n) (LVect (S i) Qubit)
controlUSTUnitary ctrl loc targetP = MkUST (controlUST' ctrl loc targetP)


controlMUST': {n : Nat} -> {i : Nat} -> {j: Nat} -> (1 controls : LVect i Qubit) -> (1 locations : LVect j Qubit) ->
                   (targetPattern : ((1_ :LVect j Qubit) -> UStateT (Unitary j) (Unitary j) (LVect j Qubit))) ->
                   (1_ :Unitary n) -> LPair (Unitary n) (LVect (i + j) Qubit)
controlMUST' {n} {i} {j} ctrl locs targetP un = let u = buildUnitary' {n = j} targetP in
  let lvControls # controls = distributeDupedLVectVect (ctrl) in 
  let qs # ts= distributeDupedLVectVect locs in
    let uc = multipleControlled i u in
      let unOut # _ = (applySafe uc un (controls ++ ts)) in
        unOut # (lvControls ++ qs)

controlMUSTUnitary: {n : Nat} -> {i : Nat} -> {j : Nat} ->(1 controls : LVect i Qubit) -> (1 locations : LVect j Qubit) ->
                   (targetPattern : ((1_ :LVect j Qubit) -> UStateT (Unitary j) (Unitary j) (LVect j Qubit)))
                   -> UStateT (Unitary n) (Unitary n) (LVect (i + j) Qubit)
controlMUSTUnitary ctrl loc targetP = MkUST (controlMUST' ctrl loc targetP)
  

export
UnitaryOp Unitary where
  applyUnitary = applyUnitarySimulated
  applyUnitaryOwn = applyUnitaryOwnSimulated
  applyControlledOwn = applyControlAbsSimulated
  adjointUST = adjointUST'
  applyParallel = applyParallelSimulated
  combineAbs= combineAbsUnitarySimulated
  run          = runUnitarySim 
  applyH = applyHSim
  applyP = applyPSim
  applyCNOT = applyCNOTSim
  exportSelf = exportUnitarySelf
  buildUnitary = buildUnitary'
  applyMultipleControlledOwn = applyMControlAbsSimulated
  controlUST = controlUSTUnitary
  multipleControlUST = controlMUSTUnitary

  



  {-
  ||| these cannot now be used as part of the interface, their usage is a but more roundabout:
  --runSplit = runSplitUnitarySim
  --applyWithSplitLVects = applyWithSplitLVectsSimulated
  --applyUnitaryAbs = applyUnitaryAbsSimulated

  private
makeSafeForAbstractControlVect : (1c:Nat) -> (1_ : Vect i Nat) -> (LPair (Nat) (Vect i Nat))

private
maximumControls: (n:Nat) -> (1_ : Vect i Nat) -> List Nat
maximumControls n [] = []
maximumControls n (k::ks) = case isLTE n k of
  Yes prf => k :: (maximumControls n ks)
  No prf => (maximumControls n ks)


smallestMissings : List Nat -> Vect i Nat -> List Nat
smallestMissings [] _ =  []
smallestMissings (x::xs) vect = (smallestMissing vect ) :: (smallestMissings xs vect)

makeSafe : List Nat -> Vect i Nat -> Vect i Nat
makeSafe [] vec = vec
makeSafe (c::cs) vec = let _ # vec = makeSafeForAbstractControlVect c vec in
                      makeSafe cs vec

  makeSafeForAbstractControlVect any [] = any # []
makeSafeForAbstractControlVect (Z) [Z] = (Z) # [Z] --invalid case in our context, no change
makeSafeForAbstractControlVect (Z) [(S m)] = (Z) # [m]
makeSafeForAbstractControlVect ((S m)) [Z] = ((S m)) # [Z]
makeSafeForAbstractControlVect (Z) (Z :: qs) = (Z) # (Z :: qs) --invalid case in our context, so whatever is fine
makeSafeForAbstractControlVect (Z) ((S m) :: qs) = let control # rest = makeSafeForAbstractControlVect (Z) qs in control # (m :: rest)
makeSafeForAbstractControlVect ((S k)) ((S m) :: qs) = case isLT k m of
  Yes prfYes => let control # rest = makeSafeForAbstractControlVect ((S k)) qs in control # (m :: rest)
  No prfNo => let control # rest = makeSafeForAbstractControlVect ((S k)) qs in control # ((S m):: rest)
makeSafeForAbstractControlVect ((S k)) (Z :: qs) = let control # rest = makeSafeForAbstractControlVect ((S k)) qs in control # ((Z) :: rest)

}