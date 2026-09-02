module CircVis 

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
runUnitarySim : {i:Nat} -> (1_: CircVis n) -> (1 _ : UStateT (CircVis n) (CircVis n) (LVect i Qubit) ) -> LPair (CircVis n) (LVect i Qubit)
runUnitarySim {i = i} un ust = runUStateT un ust

public export
runSplitUnitarySim : {i:Nat} -> {j:Nat} -> (1_: CircVis n) -> (1 _ : UStateT (CircVis n) (CircVis n) (LPair (LVect i Qubit) (LVect j Qubit)))  
                -> LPair (CircVis n) (LPair (LVect i Qubit) (LVect j Qubit))
runSplitUnitarySim {i = i} un ust = runUStateT un ust

public export
exportUnitarySelf : {i:Nat} -> (1_: CircVis n) -> (1 _ : UStateT (CircVis n) (CircVis n) (LVect i Qubit) ) -> (CircVis n) 
exportUnitarySelf un ust = let op # lvect = runUStateT un ust in
                                      let () = discardq lvect in
                                        op

||| Auxiliary function for applying a circuit to some qubits
||| this has to recognize and handle the case where it is applied within an abstract control
||| since this is the only was it can receive an lvect of qubits that contains an unexpected element, this is easy to handle 
||| using decidability.
private
applyUnitary' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> Unitary i -> (1 _ : CircVis n) -> (LPair (CircVis n) (LVect i Qubit))
applyUnitary' {n} {i} lvIn ui cn = let lvOut # vect = distributeDupedLVectVect lvIn in 
                                    let unew = U (toList vect) "U" ui cn in unew # (lvOut)
           
export
applyUnitarySimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> Unitary i -> UStateT (CircVis n) (CircVis n) (LVect i Qubit)
applyUnitarySimulated lvect ui = MkUST (applyUnitary' lvect (ui))

explicitCombineL: (1_ : LVect (S k) Qubit) -> (1_ : LVect i Qubit) -> (LVect ((S k) + i) Qubit)
explicitCombineL lvL lvR = LinearTypes.(++) lvL lvR

explicitCombine: (Vect (S k) Nat) -> (Vect i Nat) -> (Vect ((S k) + i) Nat)
explicitCombine vL vR = (++) vL vR

private ---redefinition for import convenience
duplicateLinU: (1_ : Unitary n) -> Pair (Unitary n) (Unitary n)
duplicateLinU IdGate = (IdGate, IdGate)
duplicateLinU (H j g {prf} ) = let (g1,g2) = duplicateLinU g in ((H j g1 {prf = prf}), (H j g2 {prf = prf}))
duplicateLinU (P p j g {prf}) = let (g1,g2) = duplicateLinU g in ((P p j g1 {prf = prf}), (P p j g2 {prf = prf}))
duplicateLinU (CNOT c t g {prf1} {prf2} {prf3 = prf3}) = let (g1,g2) = duplicateLinU g in ((CNOT c t g1 {prf1 = prf1} {prf2 = prf2} {prf3 = prf3}), (CNOT c t g2 {prf1 = prf1} {prf2 = prf2} {prf3 = prf3}))


private
duplicateLinC : (1 c : CircVis n) -> Pair (CircVis n) (CircVis n)
duplicateLinC IdCirc = (IdCirc, IdCirc)
duplicateLinC (U at name ui inner) = let (uil, uir) = duplicateLinU ui in
  case duplicateLinC inner of
    (l, r) => (U at name uil l, U at name uir r)


private
applyMControlSimulated': {n : Nat} -> {i : Nat} -> {k : Nat} -> (1_ : LVect (S k) Qubit) -> (1_ : LVect i Qubit) -> (1_ : CircVis i) ->
    (1_ : CircVis ( (S k) + n )) -> LPair (CircVis ((S k) + n)) (LVect ((S k) + i) Qubit)
applyMControlSimulated' {n} {i} [] ts ui usn impossible
applyMControlSimulated' {n} {i} {k = k} (c::cs) ts ui usn = 
  let lvControls # controls = distributeDupedLVectVect (c::cs) in 
    let lvOut # targets = distributeDupedLVectVect ts in 
    let (ui1, ui2) = duplicateLinC ui in
      let usnOut = (applyVis (toControlled (S k) (controls) (targets) ui1) usn (rewrite sym $ plusSuccRightSucc i k in rewrite plusCommutative i k in (controls++targets))) in
        usnOut # (lvControls ++ lvOut)

export
applyMControlAbsSimulated: {n : Nat} -> {i : Nat} -> {k : Nat} -> (1_ : LVect (S k) Qubit) -> (1_ : LVect i Qubit) -> (1_ : CircVis i) ->      
    UStateT (CircVis ((S k) + n)) (CircVis ((S k) +  n)) (LVect ((S k) +  i) Qubit)
applyMControlAbsSimulated cs ts ui = MkUST (applyMControlSimulated' cs ts ui)   


||| Helper for CircVis implementation of abstract unitary application (that is, whatever one built using UStateT)
applyUnitaryAbs': {n : Nat} -> {i : Nat} -> (1_ : UStateT (CircVis n) (CircVis n) (LVect i Qubit))      
                   -> (1 _ : CircVis n) -> LPair (CircVis n) (LVect i Qubit)
applyUnitaryAbs' ust un = 
  let (unew # lvect) = runUStateT IdCirc ust in
        let ufinal = composeVis unew un in
          do ufinal # (lvect)

||| CircVis implementation of abstract unitary application (that is, whatever one built using UStateT) 
applyUnitaryAbsSimulated : {n : Nat} -> {i : Nat} -> (1_ : UStateT (CircVis n) (CircVis n) (LVect i Qubit))      
                   -> UStateT (CircVis n) (CircVis n) (LVect i  Qubit)
applyUnitaryAbsSimulated ust = MkUST (applyUnitaryAbs' ust )


applyWithSplitLVects' : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (CircVis n) (CircVis n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> (1_: CircVis n) -> LPair (CircVis n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVects' ust (un) = 
    let ((unew) # lvect) = runUStateT IdCirc ust in
        let unew = composeVis unew un in
          do ((unew) # (lvect))

||| Implementation of abstract split application - representationally useful
applyWithSplitLVectsSimulated : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (CircVis n) (CircVis n) (LPair (LVect i Qubit) (LVect j Qubit)))
                         -> UStateT (CircVis n) (CircVis n) (LPair (LVect i Qubit) (LVect j Qubit))
applyWithSplitLVectsSimulated ust = MkUST (applyWithSplitLVects' ust)

private
combineAbs' : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : UStateT (CircVis n) (CircVis n) (LPair (LVect i Qubit) (LVect j Qubit))) -> (1 _ : CircVis n) -> (LPair (CircVis n) (LVect (i +j) Qubit))
combineAbs' ust (ui) = let (Builtin.(#) opOut (lvect #rvect)) = (runSplitUnitarySim ( ui) ust) in do
 (Builtin.(#) opOut (LinearTypes.(++) lvect rvect))

 
export
combineAbsUnitarySimulated : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : (UStateT (CircVis n) (CircVis n) (LPair (LVect i Qubit) (LVect j Qubit)) ))-> UStateT (CircVis n) (CircVis n) (LVect (i+j) Qubit)
combineAbsUnitarySimulated q = MkUST (combineAbs' q)

applyParallelSimulated': {n : Nat} -> {i : Nat} -> (1_ : UStateT (CircVis n) (CircVis n) (LVect i Qubit))     
                   -> (1_ : UStateT (CircVis n) (CircVis n) (LVect j Qubit))   
                   -> (1 _ : CircVis n) -> LPair (CircVis n) (LVect (i + j) Qubit)
applyParallelSimulated' ust1 ust2 un = 
  let (unew1# lvecti) = runUStateT IdCirc ust1 in -- there are multiple choices for what order to do what in, this is one correct one
    let (unew2 # lvectj) = runUStateT IdCirc ust2 in
        let unewest = composeVis unew1 un in
          let uOut = composeVis unew2 unewest in
            do (uOut # (lvecti ++ lvectj))

applyParallelSimulated: {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (CircVis n) (CircVis n) ((LVect i Qubit)))
                        -> (1_ : UStateT (CircVis n) (CircVis n) ((LVect j Qubit))) -> UStateT (CircVis n) (CircVis n) (LVect (i + j) Qubit)
applyParallelSimulated ust1 ust2 = MkUST (applyParallelSimulated' ust1 ust2)


private
applyUnitaryOwn' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> (1_ : CircVis i) -> (1 _ : CircVis n) -> (LPair (CircVis n) (LVect i Qubit))
applyUnitaryOwn' lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in 
                                let unew = (applyVis ui u vect) in unew # (lvOut)
           
export
applyUnitaryOwnSimulated : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> (1_ : CircVis i) -> UStateT (CircVis n) (CircVis n) (LVect i Qubit)
applyUnitaryOwnSimulated lvect ui = MkUST (applyUnitaryOwn' lvect (ui))


private
applyInternal' : {n : Nat} -> {i : Nat} -> --let lvOut # vect = distributeDupedLVectVect lvIn in ( (apply ui u vect) ) # lvOut
                (1 _ : LVect i Qubit) -> CircVis i -> (1 _ : CircVis n) -> (LPair (CircVis n) (LVect i Qubit))
applyInternal' {n} {i} lvIn ui (u) = let lvOut # vect = distributeDupedLVectVect lvIn in 
                                      let unew = (applyVis ui u vect) in unew # (lvOut)


applyInternal : {n : Nat} -> {i : Nat} ->
  (1 _ : LVect i Qubit) -> CircVis i -> UStateT (CircVis n) (CircVis n) (LVect i Qubit)
applyInternal lvect ui = MkUST (applyInternal' lvect ui)

export
applyHSim : {n : Nat} -> (1 _ : Qubit) -> UStateT (CircVis n) (CircVis n) (LVect 1 Qubit)
applyHSim q = do
    [q1] <- applyInternal {n} {i = 1} [q] (toCircVis UnitaryLinear.HGate)
    pure [q1]

export
applyPSim : {n : Nat} -> Double -> (1 _ : Qubit) -> UStateT (CircVis n) (CircVis n) (LVect 1 Qubit)
applyPSim p q = do
    [q1] <- applyInternal {n} {i = 1} [q] (toCircVis $ UnitaryLinear.PGate p)
    pure [q1]

export
applyCNOTSim : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (CircVis n) (CircVis n) (LVect 2 Qubit)
applyCNOTSim q1 q2 = do
    [q1,q2] <- applyInternal {n} {i = 2} (q1::[q2]) (toCircVis UnitaryLinear.CNOTGate)
    pure (q1::q2::[])

invert:  {n:Nat} -> (1_ : UStateT (CircVis n) (CircVis n) (LVect i Qubit)) -> (1_ : (CircVis n)) -> LPair (CircVis n) (LVect i Qubit)
invert {n} ust un =  
    let unOut # lvOut = runUStateT IdCirc ust in
      let (invFree, invDunny) = duplicateLinC unOut in
        let invu = adjointVis invFree in
          let (unFree, unDunny) = duplicateLinC un in
            let unew = composeVis invu unFree in
              unew # (lvOut)
 
export
adjointUST' : {n:Nat} -> (1_ : UStateT (CircVis n) (CircVis n) (LVect i Qubit)) -> (UStateT (CircVis n) (CircVis n) (LVect i Qubit))
adjointUST' ust = MkUST (invert ust)  


export
neutralRun' : {n:Nat} -> (1_ : UStateT (CircVis 0) (CircVis n) (LVect n Qubit)) -> CircVis n
neutralRun' ust = let op # lvect = runUStateT (IdCirc {n = 0}) ust in
                        let () = discardq lvect in
                          op 

export
buildUnitary': {n:Nat} -> ((1_ : LVect n Qubit) -> (UStateT (CircVis n) (CircVis n) (LVect n Qubit))) -> CircVis n
buildUnitary' {n} f = let ( cvis # qs )= newQubitsVis0' n (IdCirc {n = 0}) in exportUnitarySelf (IdCirc {n = n}) (f qs)


controlMUST': {n : Nat} -> {i : Nat} -> {j: Nat} -> (1 controls : LVect i Qubit) -> (1 locations : LVect j Qubit) ->
                   (targetPattern : ((1_ :LVect j Qubit) -> UStateT (CircVis j) (CircVis j) (LVect j Qubit))) ->
                   (1_ :CircVis n) -> LPair (CircVis n) (LVect (i + j) Qubit)
controlMUST' {n} {i} {j} ctrl locs targetP un = 
  let u = buildUnitary' {n = j} targetP in
    let lvControls # controls = distributeDupedLVectVect (ctrl) in 
        let qs # ts = distributeDupedLVectVect locs in
             let (ui1, ui2) = duplicateLinC u in
                 let usnOut = (composeVis (toControlledN n (controls) (ts) ui1) un) in
                     usnOut # (lvControls ++ qs)

controlMUSTUnitary: {n : Nat} -> {i : Nat} -> {j : Nat} ->(1 controls : LVect i Qubit) -> (1 locations : LVect j Qubit) ->
                   (targetPattern : ((1_ :LVect j Qubit) -> UStateT (CircVis j) (CircVis j) (LVect j Qubit)))
                   -> UStateT (CircVis n) (CircVis n) (LVect (i + j) Qubit)
controlMUSTUnitary ctrl loc targetP = MkUST (controlMUST' ctrl loc targetP)
  

export
UnitaryOp CircVis where
  applyUnitary = applyUnitarySimulated
  applyUnitaryOwn = applyUnitaryOwnSimulated
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
  multipleControlUST = controlMUSTUnitary

  


