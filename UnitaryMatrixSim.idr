module UnitaryMatrixSim

import Matrix
import Data.Vect
import Data.Nat
import Complex
import Lemmas
import QuantumOp
import UnitaryLinear
import UStateT
import LinearTypes
{-}
export
fromUtoM : {n : Nat} -> Unitary n -> Matrix (power 2 n) (power 2 n)
fromUtoM {n} IdGate = (matrixId (power 2 n)) 
fromUtoM {n} (H j (gate))= let k = minus (minus n 1) j in (simpleTensor matrixH n k) `matrixMult` (fromUtoM gate)
fromUtoM {n} (P p j (gate)) = let k = minus (minus n 1) j in  (simpleTensor (matrixP p) n k)  `matrixMult` (fromUtoM gate)
fromUtoM {n} (CNOT c t (gate)) = 
  let ci = minus (minus n 1) c in 
  let ti = minus (minus n 1) t in 
  (tensorCNOT n ci ti) `matrixMult` (fromUtoM gate) 


export
fromUtoM : {n : Nat} -> Unitary n -> Matrix (power 2 n) (power 2 n)
fromUtoM {n} IdGate = (matrixId (power 2 n)) 
fromUtoM {n} (H j (gate))= (simpleTensor matrixH n j) `matrixMult` (fromUtoM gate)
fromUtoM {n} (P p j (gate)) = (simpleTensor (matrixP p) n j)  `matrixMult` (fromUtoM gate)
fromUtoM {n} (CNOT c t (gate)) = (tensorCNOT n c t) `matrixMult` (fromUtoM gate) 
  -}

export
unitaryToMatrix : {n : Nat} -> Unitary n -> Matrix (power 2 n) (power 2 n)
unitaryToMatrix {n} IdGate = matrixId (power 2 n)
unitaryToMatrix {n} (H j u) =
  matrixMult (simpleTensor matrixH n j) (unitaryToMatrix u)
unitaryToMatrix {n} (P p j u) =
  matrixMult (simpleTensor (matrixP p) n j) (unitaryToMatrix u)
unitaryToMatrix {n} (CNOT c t u) =
  matrixMult (tensorCNOT n c t) (unitaryToMatrix u)


export
fromUtoUM : {n : Nat} -> Unitary n -> UnitaryMatrix n
fromUtoUM un = unitaryToMatrix un


applyUnitaryOwnMatrixSim' : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) ->  (1_ : UnitaryMatrix i) -> 
                         (1_: UnitaryMatrix n) -> LPair (UnitaryMatrix n) (LVect i Qubit)
applyUnitaryOwnMatrixSim'{n} {i} qubits umi umn = 
  let (umi1, umi2) = dupMatrixCD umi in
    let (umnFree, vac) = dupMatrixCD umn in
      let lq # q = distributeDupedLVectVect qubits in
        let uOut = matrixMult (applyUM (q) (umi1)) umnFree in
        uOut # lq


applyUnitaryOwnMatrixSim : {n : Nat} -> {i : Nat} ->  (1 _ : LVect i Qubit) -> (1_ : UnitaryMatrix i) -> UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect i Qubit)
applyUnitaryOwnMatrixSim qubits ui = MkUST (applyUnitaryOwnMatrixSim' qubits ui)


applyUnitaryMatrixSim' : {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> Unitary i -> 
                         (1_: UnitaryMatrix n) -> LPair (UnitaryMatrix n) (LVect i Qubit)
applyUnitaryMatrixSim'{n} {i} qubits ui umn =  --applyUnitaryOwnMatrixSim'{n} {i} qubits (fromUtoUM ui) umn {-}
    let lq # q = distributeDupedLVectVect qubits in
      let (umnFree, vac) = dupMatrixCD umn in
        let ui2n # _ = applySafe ui (IdGate{n=n}) q  in
          let umi2n = fromUtoUM ui2n in
            let uOut = matrixMult umi2n umnFree in
              uOut # lq 


applyUnitaryMatrixSim : {n : Nat} -> {i : Nat} -> 
                 (1 _ : LVect i Qubit) -> Unitary i -> UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect i Qubit)
applyUnitaryMatrixSim qubits ui = MkUST (applyUnitaryMatrixSim' qubits ui)


applyHMatrixSim' : {n : Nat} -> (1 _ : Qubit) -> 
                         (1_: UnitaryMatrix n) -> LPair (UnitaryMatrix n) (LVect 1 Qubit)
applyHMatrixSim'{n} qubit umn = 
  let (q, k) = qubitToNatPair qubit  in
    let (umnFree, vac) = dupMatrixCD umn in
      let left = simpleTensor matrixH n k in
        (left `matrixMult` umnFree) # [q]


applyHMatrixSim : {n : Nat} -> (1 _ : Qubit) -> UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect 1 Qubit)
applyHMatrixSim qubit = MkUST (applyHMatrixSim' qubit)


applyPMatrixSim' : {n : Nat} -> (1 _ : Qubit) -> (p:Double) -> 
                         (1_: UnitaryMatrix n) -> LPair (UnitaryMatrix n) (LVect 1 Qubit)
applyPMatrixSim'{n} qubit p umn = 
  let (q, k) = qubitToNatPair qubit  in
    let (umnFree, vac) = dupMatrixCD umn in
      let left = simpleTensor (matrixP p) n k in
        (left `matrixMult` umnFree) # [q]


applyPMatrixSim : {n : Nat} -> (p:Double) -> (1 _ : Qubit) -> UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect 1 Qubit)
applyPMatrixSim p qubit = MkUST (applyPMatrixSim' qubit p)


applyCNOTMatrixSim' : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) ->
                         (1_: UnitaryMatrix n) -> LPair (UnitaryMatrix n) (LVect 2 Qubit)
applyCNOTMatrixSim'{n} c t umn = 
  let (c, i) = qubitToNatPair c  in
   let (t, j) = qubitToNatPair t  in 
    let (umnFree, vac) = dupMatrixCD umn in
      let left = tensorCNOT n i j in
        (left `matrixMult` umnFree) # [c,t]


applyCNOTMatrixSim : {n : Nat} -> (1 _ : Qubit) -> (1 _ : Qubit) -> UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect 2 Qubit)
applyCNOTMatrixSim c t = MkUST (applyCNOTMatrixSim' c t)


adjointUSTMatrixSim': {n : Nat} ->(1_ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect i Qubit)) -> (1_ : UnitaryMatrix n) -> LPair (UnitaryMatrix n) (LVect i Qubit)
adjointUSTMatrixSim'{n} ust um = let un # lvOut = runUStateT (idU) ust in
        let (uni1, vac) = dupMatrixCD un in
          let (umFree, vac) = dupMatrixCD um in
            let invu = adjoint uni1 in
              let unew = invu `matrixMult` umFree in
                unew # (lvOut)

adjointUSTMatrixSim: {n : Nat} -> (1_ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect i Qubit)) -> (UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect i Qubit))
adjointUSTMatrixSim {n} ust = MkUST (adjointUSTMatrixSim' ust)


applyControlledMatrix': {n : Nat} -> {i : Nat} -> (1 control : Qubit) -> (1 targets : LVect i Qubit) -> (1 ownUnitary : UnitaryMatrix i)      
                   -> (1_ : UnitaryMatrix (S n)) -> LPair (UnitaryMatrix  (S n)) (LVect (S i) Qubit)
applyControlledMatrix' {n} {i} c ts umi umsn = 
  let (umi1, vac1) = dupMatrixCD umi in
    let (umsnFree, vac) = dupMatrixCD umsn in
      let controlled = controlUnitaryPow umi1 in
        let (c, k) = qubitToNatPair c in 
          let (ts # ks) = distributeDupedLVectVect ts in
            let uOut = matrixMult (applyUM {n = S n} (k::ks) (controlled)) umsnFree in
            uOut # (c::ts)
            


applyControlledMatrix: {n : Nat} -> {i : Nat} -> (1 controls : Qubit) -> (1 targets : LVect i Qubit) -> (1 ownUnitary : UnitaryMatrix  i)      
                   -> UStateT (UnitaryMatrix (S n)) (UnitaryMatrix  (S n)) (LVect (S i) Qubit)
applyControlledMatrix c ts umi = MkUST $ applyControlledMatrix' c ts umi



applyMultipleControlledOwnMatrix': {n : Nat} -> {i : Nat} -> {k: Nat} -> (1 controls : LVect (S k) Qubit) -> (1 targets : LVect i Qubit) -> (1 ownUnitary : UnitaryMatrix i)      
                   -> (1_ : UnitaryMatrix ((S k) + n)) -> LPair (UnitaryMatrix ((S k) + n)) (LVect ((S k) + i ) Qubit)
applyMultipleControlledOwnMatrix' {n} {i} {k} cs ts umi umsn = 
  let (umi1, vac1) = dupMatrixCD umi in
    let (umsnFree, vac2) = dupMatrixCD umsn in
    let lvControls # controls = distributeDupedLVectVect (cs) in 
        let (ts # targets) = distributeDupedLVectVect ts in
          let controlled = multipleControlledUnitary (S k) umi1 in
            let uOut = matrixMult (applyUM {n = S k + n} (controls++targets) (controlled)) umsnFree in
            uOut# (lvControls ++ ts)
                

applyMultipleControlledOwnMatrix: {n : Nat} -> {i : Nat} -> {k:Nat} -> (1 controls : LVect (S k) Qubit) -> (1 targets : LVect i Qubit) -> (1 ownUnitary : UnitaryMatrix i)      
                   -> UStateT (UnitaryMatrix ((S k) + n)) (UnitaryMatrix ((S k) + n)) (LVect ((S k)+ i ) Qubit)
applyMultipleControlledOwnMatrix cs ts umi = MkUST $ applyMultipleControlledOwnMatrix' cs ts umi

applyParallelMatrix': {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) ((LVect i Qubit)))
                        -> (1_ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) ((LVect j Qubit))) -> (1_ : UnitaryMatrix n) -> LPair (UnitaryMatrix n) (LVect (i + j) Qubit)
applyParallelMatrix' {i} {j} {n} ust1 ust2 umn =
    let (unew1# lvecti) = runUStateT (idU) ust1 in -- there are multiple choices for what order to do what in, this is one correct one
      let (unew2 # lvectj) = runUStateT (idU) ust2  in
        let (unew1Free, vac1) = dupMatrixCD unew1 in
          let (unew2Free, vac1) = dupMatrixCD unew2 in
            let (umnFree, vac1) = dupMatrixCD umn in
              let unewest = unew1Free `matrixMult` umnFree in
                let uOut = unew2Free `matrixMult` unewest in
                  do (uOut # (lvecti ++ lvectj))
 
applyParallelMatrixSim : {n : Nat} -> {i : Nat} -> {j : Nat} -> (1_ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) ((LVect i Qubit)))
                        -> (1_ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) ((LVect j Qubit))) -> UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect (i + j) Qubit)
applyParallelMatrixSim ust1 ust2 = MkUST (applyParallelMatrix' ust1 ust2)         

public export
runUnitaryMatrixSim : {i:Nat} -> (1_: UnitaryMatrix n) -> (1 _ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect i Qubit) ) -> LPair (UnitaryMatrix n) (LVect i Qubit)
runUnitaryMatrixSim {i = i} un ust = runUStateT un ust

public export
runSplitUnitaryMatrixSim : {i:Nat} -> {j:Nat} -> (1_: UnitaryMatrix n) -> (1 _ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LPair (LVect i Qubit) (LVect j Qubit)))  
                -> LPair (UnitaryMatrix n) (LPair (LVect i Qubit) (LVect j Qubit))
runSplitUnitaryMatrixSim {i = i} un ust = runUStateT un ust

private
combineAbs' : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LPair (LVect i Qubit) (LVect j Qubit))) -> (1 _ : UnitaryMatrix n) -> (LPair (UnitaryMatrix n) (LVect (i +j) Qubit))
combineAbs' ust (ui) = let (Builtin.(#) opOut (lvect #rvect)) = (runSplitUnitaryMatrixSim ( ui) ust) in do
 (Builtin.(#) opOut (LinearTypes.(++) lvect rvect))

 
export
combineAbsUnitaryMatrixSim : {n : Nat} -> {i : Nat} -> {j:Nat} ->
  (1_ : (UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LPair (LVect i Qubit) (LVect j Qubit)) ))-> UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect (i+j) Qubit)
combineAbsUnitaryMatrixSim q = MkUST (combineAbs' q)


controlMUST': {n : Nat} -> {i : Nat} -> {j: Nat} -> (1 controls : LVect i Qubit) -> (1 locations : LVect j Qubit) ->
                   (targetPattern : ((1_ :LVect j Qubit) -> UStateT (UnitaryMatrix j) (UnitaryMatrix j) (LVect j Qubit))) ->
                   (1_ :UnitaryMatrix n) -> LPair (UnitaryMatrix n) (LVect (i + j) Qubit)
controlMUST' {n} {i} {j} ctrl locs targetP un = let u = buildUnitaryM {n = j} targetP in
  let (unFree, vac) = dupMatrixCD un in
  let lvControls # controls = distributeDupedLVectVect (ctrl) in 
  let qs # ts= distributeDupedLVectVect locs in
    let uc = multipleControlledUnitary i u in
      let unOut = matrixMult (applyUM (controls++ts) (uc)) unFree in
        unOut # (lvControls ++ qs)

controlMUSTUnitaryMatrix: {n : Nat} -> {i : Nat} -> {j : Nat} ->(1 controls : LVect i Qubit) -> (1 locations : LVect j Qubit) ->
                   (targetPattern : ((1_ :LVect j Qubit) -> UStateT (UnitaryMatrix j) (UnitaryMatrix j) (LVect j Qubit)))
                   -> UStateT (UnitaryMatrix n) (UnitaryMatrix n) (LVect (i + j) Qubit)
controlMUSTUnitaryMatrix ctrl loc targetP = MkUST (controlMUST' ctrl loc targetP)


export
UnitaryOp UnitaryMatrix where
  applyUnitary = applyUnitaryMatrixSim
  applyUnitaryOwn = applyUnitaryOwnMatrixSim
  applyControlledOwn = applyControlledMatrix
  adjointUST = adjointUSTMatrixSim
  applyParallel = applyParallelMatrixSim
  run          = runUnitaryMatrixSim
  applyH = applyHMatrixSim
  applyP = applyPMatrixSim
  applyCNOT = applyCNOTMatrixSim
  exportSelf = exportUnitaryMatrixSelf
  combineAbs = combineAbsUnitaryMatrixSim
  applyMultipleControlledOwn = applyMultipleControlledOwnMatrix
  buildUnitary = buildUnitaryM
  multipleControlUST = controlMUSTUnitaryMatrix


