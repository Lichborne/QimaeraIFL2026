module UnitaryNoPrfSim

import Data.Vect
import Data.Nat
import Data.Vect.Sort
import Decidable.Equality
import Injection
import Lemmas
import UnitaryLinear
import UnitaryNoPrf
import UStateT
import LinearTypes
import QStateT
import QuantumOp
import SimulatedOp


public export
runUnitaryNoPrfSim : {i:Nat} -> (1_: UnitaryNoPrf n) -> (1 _ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit) ) -> LPair (UnitaryNoPrf n) (LVect i Qubit)
runUnitaryNoPrfSim {i = i} simop ust = runUStateT simop ust


public export
exportSelf' : {i:Nat} -> (1_: UnitaryNoPrf n) -> (1 _ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit) ) -> UnitaryNoPrf n
exportSelf' {i = i} simop ust = let unprf # lvect = runUStateT simop ust in
                                      let () = discardq lvect in
                                          unprf

public export
runSplitUnitaryNoPrfSim : {i:Nat} -> {j:Nat} -> (1_: UnitaryNoPrf n) -> (1 _ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))  
                -> LPair (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit))
runSplitUnitaryNoPrfSim {i = i} simop ust = runUStateT simop ust

||| Auxiliary function for applying a circuit to some qubits
private
applyUnitaryNoPrf' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> UnitaryNoPrf i -> (1 _ : UnitaryNoPrf n) -> (LPair (UnitaryNoPrf n) (LVect i Qubit))
applyUnitaryNoPrf' lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in 
          let unew = (UnitaryNoPrf.apply ui u vect) in unew # (lvOut)
export
applyUnitaryNoPrfSimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit)
applyUnitaryNoPrfSimulated lvect ui = MkUST (applyUnitaryNoPrf' lvect (toNoPrf ui))

private
applyUnitaryNoPrfOwn' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> (1_ : UnitaryNoPrf i) -> (1 _ : UnitaryNoPrf n) -> (LPair (UnitaryNoPrf n) (LVect i Qubit))
applyUnitaryNoPrfOwn' lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in 
  case decInj (n) vect of 
            Yes prfYes => let unew = (UnitaryNoPrf.apply ui u vect) in unew # (lvOut)
            No prfNo => let applicable = clampUniqueWithCap n vect in --SEE UNITARYSIMULATED FOR MORE DETAIL
                          let un = (UnitaryNoPrf.apply ui u (applicable)) in un # lvOut 
export
applyUnitaryNoPrfOwnSimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> (1_ : UnitaryNoPrf i) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit)
applyUnitaryNoPrfOwnSimulated lvect ui = MkUST (applyUnitaryNoPrfOwn' lvect (ui))

applyInternal : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> UnitaryNoPrf i -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit)
applyInternal lvect ui = MkUST (applyUnitaryNoPrf' lvect ui)


private
applyControlSimulated': {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : LVect i Qubit) -> (1_ : UnitaryNoPrf i) ->
    (1_ : UnitaryNoPrf (S n)) -> LPair (UnitaryNoPrf (S n)) (LVect (S i) Qubit)
applyControlSimulated' {n} {i} c ts ui usn = 
  let (c, k) = qubitToNatPair c in
    let lvOut # targets = distributeDupedLVectVect ts in 
      let usnOut=  (UnitaryNoPrf.apply (controlled ui) usn (k::targets)) in
        usnOut # (c :: lvOut)

export
applyControlAbsSimulated: {n : Nat} -> {i : Nat} -> (1 _ : Qubit) -> (1_ : LVect i Qubit) -> (1_ : UnitaryNoPrf i) ->      
    UStateT (UnitaryNoPrf (S n)) (UnitaryNoPrf (S n)) (LVect (S i) Qubit)
applyControlAbsSimulated c ts ui = MkUST (applyControlSimulated' c ts ui)  

public export
duplicateLinU: (1_ : UnitaryNoPrf n) -> Pair (UnitaryNoPrf n) (UnitaryNoPrf n)
duplicateLinU IdGate = (IdGate, IdGate)
duplicateLinU (H j g  ) = let (g1,g2) = duplicateLinU g in ((H j g1), (H j g2 ))
duplicateLinU (P p j g ) = let (g1,g2) = duplicateLinU g in ((P p j g1), (P p j g2 ))
duplicateLinU (CNOT c t g) = let (g1,g2) = duplicateLinU g in ((CNOT c t g1), (CNOT c t g2))

||| Helper for UnitaryNoPrf implementation of abstract UnitaryNoPrf application (that is, whatever one built using UStateT)
applyUnitaryNoPrfAbs': {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))      
                   -> (1 _ : UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LVect i Qubit)
applyUnitaryNoPrfAbs' ust un = 
  let (unew # lvect) = runUStateT IdGate ust in
        let ufinal = UnitaryNoPrf.compose unew un in
          do ufinal # (lvect)

||| UnitaryNoPrf implementation of abstract UnitaryNoPrf application (that is, whatever one built using UStateT) 
applyUnitaryNoPrfAbsSimulated : {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))      
                   -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i  Qubit)
applyUnitaryNoPrfAbsSimulated ust = MkUST (applyUnitaryNoPrfAbs' ust )


applyUnitaryNoPrfAbsSplit' : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> (1_: UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit))
applyUnitaryNoPrfAbsSplit' ust (un) = 
  let ((unew) # lvect) = runUStateT IdGate ust in
        let unew = UnitaryNoPrf.compose unew un in
          do ((unew) # (lvect))

||| Implementation of abstract split application - representationally useful
applyUnitaryNoPrfAbsSplitSimulated : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit))
applyUnitaryNoPrfAbsSplitSimulated ust = MkUST (applyUnitaryNoPrfAbsSplit' ust)

||| Helper for implementation of abstract controlled split application 
applyControlledUSplitSim' : {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))
                             -> (1_ : UnitaryNoPrf (S n)) -> LPair (UnitaryNoPrf (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledUSplitSim' q ust (usn)= 
  let (q, k) = qubitToNatPair q in
    let un # (lvLeft # lvRight) = runUStateT (IdGate {n = n}) ust in
      let lvMid # vect = distributeDupedLVectVect (lvLeft ++ lvRight) in
        let lvOutL # lvOutR = splitLVinto i j lvMid in 
          let checkIfControl = (length (maximumControls n vect)) in
          case isGT checkIfControl 0 of 
            No prfNo => let vn = findInLin k (makeNeutralVectN (S n)) in let un = (UnitaryNoPrf.apply (controlled un) usn (k::vn)) in un # (q :: lvOutL # lvOutR)
            Yes prfYes => let v = makeNeutralVectN (S n) in let vn = findInLin k v in   
              case decInj (S n) (k :: vn) of 
                Yes prfYes => let unew = (UnitaryNoPrf.apply (controlled un) usn (k :: vn)) in                          
                                unew # (q :: lvOutL # lvOutR)
                No prfNo => let applicableSn = makeNeutralVectN (S n) in --SEE UNITARYSIMULATED FOR MORE DETAIL
                            let un = (UnitaryNoPrf.apply (controlled un) usn (applicableSn)) in 
                                un # (q :: lvOutL # lvOutR)

||| Implementation of abstract controlled split application     
applyControlledSimulatedSplit: {i:Nat} -> {j:Nat} -> {n : Nat} -> (1 _ : Qubit) -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)))
                             -> UStateT (UnitaryNoPrf (S n)) (UnitaryNoPrf (S n)) (LPair (LVect (S (i)) Qubit) (LVect j Qubit))
applyControlledSimulatedSplit ctrl ust = MkUST (applyControlledUSplitSim' ctrl ust)   


private
combineAbs' : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit))) -> (1 _ : UnitaryNoPrf n) -> (LPair (UnitaryNoPrf n) (LVect (i +j) Qubit))
combineAbs' ust (ui) = let (Builtin.(#) opOut (lvect #rvect)) = (runSplitUnitaryNoPrfSim ( ui) ust) in do
 (Builtin.(#) opOut (LinearTypes.(++) lvect rvect))

 
export
combineAbsUnitaryNoPrfSimulated : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : (UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LPair (LVect i Qubit) (LVect j Qubit)) ))-> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect (i+j) Qubit)
combineAbsUnitaryNoPrfSimulated q = MkUST (combineAbs' q)

explicitCombineL: (1_ : LVect (S k) Qubit) -> (1_ : LVect i Qubit) -> (LVect ((S k) + i) Qubit)
explicitCombineL lvL lvR = LinearTypes.(++) lvL lvR

explicitCombine: (Vect (S k) Nat) -> (Vect i Nat) -> (Vect ((S k) + i) Nat)
explicitCombine vL vR = (++) vL vR

export
applyHSim : {n : Nat} -> (1 _ : Qubit) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect 1 Qubit)
applyHSim q = do
    [q1] <- applyInternal {n} {i = 1} [q] (UnitaryNoPrf.HGate)
    pure [q1]

export
applyPSim : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect 1 Qubit)
applyPSim p q = do
    [q1] <- applyInternal {n} {i = 1} [q] (UnitaryNoPrf.PGate p)
    pure [q1]

export
applyCNOTSim : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect 2 Qubit)
applyCNOTSim q1 q2 = do
    [q1,q2] <- applyInternal {n} {i = 2} (q1::[q2]) UnitaryNoPrf.CNOTGate
    pure (q1::q2::[])

private
invertNoPrf: (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit)) -> (1_ : (UnitaryNoPrf n)) -> LPair (UnitaryNoPrf n) (LVect i Qubit)
invertNoPrf ust un =  
    let unOut # lvOut = runUStateT IdGate ust in
      let (invFree, invDunny) = duplicateLinU unOut in
        let invu = adjoint invFree in
          let (unFree, unDunny) = duplicateLinU un in
            let unew = compose invu unFree in
              unew # (lvOut)
 
export
adjointUSTNoPrf' :  {n:Nat} ->  (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit)) -> (UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))
adjointUSTNoPrf' ust = MkUST (invertNoPrf ust)

export
neutralRun' : {n:Nat} -> (1_ : UStateT (UnitaryNoPrf 0) (UnitaryNoPrf n) (LVect n Qubit)) -> UnitaryNoPrf n
neutralRun' ust = let op # lvect = runUStateT (IdGate {n = 0}) ust in
                        let () = discardq lvect in
                          op 


applyParallelSimulatedNoPrf': {n : Nat} -> {i : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect i Qubit))     
                   -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect j Qubit))   
                   -> (1 _ : UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LVect (i + j) Qubit)
applyParallelSimulatedNoPrf' ust1 ust2 un = 
    let (unew1 # lvecti) = runUStateT IdGate ust1 in
      let (unew2 # lvectj) = runUStateT IdGate ust2 in
        let umed = UnitaryNoPrf.compose unew1 un in
          let ufinal = UnitaryNoPrf.compose unew2 umed in
            do ufinal # (lvecti ++ lvectj)

export 
applyParallelSimulatedNoPrf: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) ((LVect i Qubit)))
                        -> (1_ : UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) ((LVect j Qubit))) -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect (i + j) Qubit)
applyParallelSimulatedNoPrf ust1 ust2 = MkUST (applyParallelSimulatedNoPrf' ust1 ust2)

export
buildUnitaryNoPrf': {n:Nat} -> ((1_ : LVect n Qubit) -> (UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect n Qubit))) -> UnitaryNoPrf n
buildUnitaryNoPrf' {n} f = neutralRun' (do
  qs <- supplyQubits n
  qsOut <- applyUStateT (f qs)
  pure qsOut)

  
controlUST': {n : Nat} -> {i : Nat} -> (1 control : Qubit) -> (1 locations : LVect i Qubit) ->
                   (targetPattern : ((1_ :LVect i Qubit) -> UStateT (UnitaryNoPrf i) (UnitaryNoPrf i) (LVect i Qubit)))
                   -> (1_ :UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LVect (S i) Qubit)
controlUST' {n} {i} ctrl locs targetP un = let u = buildUnitaryNoPrf' {n = i} targetP in
  let (q, c) = qubitToNatPair ctrl in
  let qs # ts= distributeDupedLVectVect locs in
    let uc = controlled u in
      let unOut  = (UnitaryNoPrf.apply uc un (c::ts)) in
        unOut # (q::qs)


controlUSTUnitaryNoPrf: {n : Nat} -> {i : Nat} -> (1 control : Qubit) -> (1 locations : LVect i Qubit) ->
                   (targetPattern : ((1_ :LVect i Qubit) -> UStateT (UnitaryNoPrf i) (UnitaryNoPrf i) (LVect i Qubit)))
                   -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect (S i) Qubit)
controlUSTUnitaryNoPrf ctrl loc targetP = MkUST (controlUST' ctrl loc targetP)


private
applyMControlSimulatedNoPrf': {n : Nat} -> {i : Nat} -> {k : Nat} -> (1_ : LVect (S k) Qubit) -> (1_ : LVect i Qubit) -> (1_ : UnitaryNoPrf i) ->
    (1_ : UnitaryNoPrf ( (S k) + n )) -> LPair (UnitaryNoPrf ((S k) + n)) (LVect ((S k) + i) Qubit)
applyMControlSimulatedNoPrf' {n} {i} [] ts ui usn impossible
applyMControlSimulatedNoPrf' {n} {i} {k = k} (c::cs) ts ui usn = 
  let lvControls # controls = distributeDupedLVectVect (c::cs) in 
    let lvOut # targets = distributeDupedLVectVect ts in 
      let usnOut = (UnitaryNoPrf.apply (UnitaryNoPrf.multipleControlled (S k) ui) usn (explicitCombine controls targets)) in
        usnOut # (lvControls ++ lvOut)

export
applyMControlSimulatedNoPrf: {n : Nat} -> {i : Nat} -> {k : Nat} -> (1_ : LVect (S k) Qubit) -> (1_ : LVect i Qubit) -> (1_ : UnitaryNoPrf i) ->      
    UStateT (UnitaryNoPrf ((S k) + n)) (UnitaryNoPrf ((S k) +  n)) (LVect ((S k) +  i) Qubit)
applyMControlSimulatedNoPrf cs ts ui = MkUST (applyMControlSimulatedNoPrf' cs ts ui)   

||| helper for multiple control implementation
controlMUST': {n : Nat} -> {i : Nat} -> {j: Nat} -> (1 controls : LVect i Qubit) -> (1 locations : LVect j Qubit) ->
                   (targetPattern : ((1_ :LVect j Qubit) -> UStateT (UnitaryNoPrf j) (UnitaryNoPrf j) (LVect j Qubit))) ->
                   (1_ :UnitaryNoPrf n) -> LPair (UnitaryNoPrf n) (LVect (i + j) Qubit)
controlMUST' {n} {i} {j} ctrl locs targetP un = let u = buildUnitaryNoPrf' {n = j} targetP in
  let lvControls # controls = distributeDupedLVectVect (ctrl) in 
  let qs # ts= distributeDupedLVectVect locs in
    let uc = multipleControlled i u in
      let unOut = (UnitaryNoPrf.apply uc un (controls ++ ts)) in
        unOut # (lvControls ++ qs)

||| multiple control implementation for UnitaryNoPrfß
controlMUSTUnitaryNoPrf: {n : Nat} -> {i : Nat} -> {j : Nat} ->(1 controls : LVect i Qubit) -> (1 locations : LVect j Qubit) ->
                   (targetPattern : ((1_ :LVect j Qubit) -> UStateT (UnitaryNoPrf j) (UnitaryNoPrf j) (LVect j Qubit)))
                   -> UStateT (UnitaryNoPrf n) (UnitaryNoPrf n) (LVect (i + j) Qubit)
controlMUSTUnitaryNoPrf ctrl loc targetP = MkUST (controlMUST' ctrl loc targetP)


export
UnitaryOp UnitaryNoPrf where
  applyUnitary = applyUnitaryNoPrfSimulated
  applyUnitaryOwn = applyUnitaryNoPrfOwnSimulated
  applyControlledOwn = applyControlAbsSimulated
  adjointUST = adjointUSTNoPrf'
  applyParallel = applyParallelSimulatedNoPrf
  combineAbs= combineAbsUnitaryNoPrfSimulated
  run          = runUnitaryNoPrfSim 
  applyH = applyHSim
  applyP = applyPSim
  applyCNOT = applyCNOTSim
  exportSelf = exportSelf'
  buildUnitary = buildUnitaryNoPrf'
  controlUST= controlUSTUnitaryNoPrf
  applyMultipleControlledOwn = applyMControlSimulatedNoPrf
  multipleControlUST = controlMUSTUnitaryNoPrf



{-
  ||| these cannot now be used as part of the interface, their usage is a but more roundabout:
    --runSplit = runSplitUnitaryNoPrfSim
    --applyWithSplitLVects = applyUnitaryNoPrfAbsSplitSimulated
    --applyUnitaryAbs = applyUnitaryNoPrfAbsSimulated
-}