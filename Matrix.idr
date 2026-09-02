module Matrix

import Data.Vect
import Data.Nat
import Complex
import Lemmas
import Decidable.Equality
import NatRules
import Data.List
import Data.Vect.Sort
import Data.Vect.Elem

%default total

public export
Matrix : Nat -> Nat ->  Type
Matrix n m = Vect n (Vect m (Complex Double))

public export
Vector : Nat -> Type
Vector n = Vect n (Complex Double)


export
idRow : (n : Nat) -> Nat -> Vector n
idRow 0 _ = []
idRow (S k) 0 = 1 :: idRow k (S k)
idRow (S k) (S p) = 0 :: idRow k p

export
matrixId : (n : Nat) -> Matrix n n
matrixId n = matrixId' n 0 n where
  matrixId' : (k : Nat) -> (p : Nat) -> (n : Nat) -> Matrix k n
  matrixId' 0 p n = []
  matrixId' (S k) p n = (idRow n p) :: matrixId' k (S p) n

export
addVector : Vector n -> Vector n -> Vector n
addVector [] [] = []
addVector (x::xs) (y::ys) = (x+y) :: (addVector xs ys)

export
addMatrix : Matrix n m -> Matrix n m -> Matrix n m
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = (addVector x y) :: (addMatrix xs ys)

private
vectProduct : Vector n -> Vector n -> Complex Double
vectProduct [] [] = 0
vectProduct (x :: xs) (y :: ys) = x * y + vectProduct xs ys

export
makeCol : Vector n -> Matrix n 1
makeCol [] = []
makeCol (x :: xs) = [x] :: makeCol xs

private
addCol : Vector n -> Matrix n p -> Matrix n (S p)
addCol [] [] = []
addCol (x :: xs) (v :: vs) = (x :: v) :: addCol xs vs

export
transposeMatrix : {n : Nat} -> {p : Nat} ->  Matrix n p -> Matrix p n
transposeMatrix [] = replicate _ []
transposeMatrix (x :: xs) = addCol x (transposeMatrix xs)

export
multVectMatrix : {n : Nat} -> {p : Nat} ->  Vector n -> Matrix n p -> Vector p
multVectMatrix v m =
  let mt = transposeMatrix m in multVectMatrix' v mt where
    multVectMatrix' : Vector l -> Matrix k l -> Vector k
    multVectMatrix' v [] = []
    multVectMatrix' v (x :: xs) = (vectProduct v x) :: multVectMatrix' v xs

export
matrixMult : {n : Nat} -> {m : Nat} -> {p : Nat} -> Matrix n m -> Matrix m p -> Matrix n p
matrixMult [] ys = []
matrixMult (x :: xs) ys = (multVectMatrix x ys) :: matrixMult xs ys

export
multScalarVect : Complex Double -> Vector n -> Vector n
multScalarVect _ [] = []
multScalarVect x (y :: ys) = (x * y) :: multScalarVect x ys

export
multScalarMatrix : Complex Double -> Matrix n m -> Matrix n m
multScalarMatrix _ [] = []
multScalarMatrix x (y :: ys) = multScalarVect x y :: multScalarMatrix x ys

private
concatRows : Matrix n p -> Matrix n q -> Matrix n (p + q)
concatRows [] [] = []
concatRows (x :: xs) (y :: ys) = (x ++ y) :: (concatRows xs ys)

private
concatCols : Matrix n p -> Matrix m p -> Matrix (n + m) p
concatCols v w = v ++ w

private
tensorProduct' : Vector (S n) -> Matrix p r -> Matrix p ((S n) * r)
tensorProduct' [x] m = rewrite multZeroLeftZero r in rewrite plusZeroRightNeutral r in multScalarMatrix x m
tensorProduct' (x :: y :: ys) m = (multScalarMatrix x m) `concatRows` (tensorProduct' (y :: ys) m)

export
tensorProduct : Matrix n (S m) -> Matrix p r -> Matrix (n * p) ((S m) * r)
tensorProduct [] _ = []
tensorProduct [v] xs = rewrite multZeroLeftZero p in rewrite plusZeroRightNeutral p in tensorProduct' v xs
tensorProduct (v :: w :: vs) xs = (tensorProduct' v xs) `concatCols` (tensorProduct (assert_smaller (v::w::vs) (w :: vs)) xs)

private
tensorRow : {p:Nat} -> Vector m -> Matrix p r -> Matrix p (m * r)
tensorRow {p} []       xs = replicate _ []
tensorRow (x :: v) xs = (multScalarMatrix x xs) `concatRows` (tensorRow v xs)

export
tensorProductAny : {p:Nat} -> Matrix n m -> Matrix p r -> Matrix (n * p) (m * r)
tensorProductAny []       _  = []
tensorProductAny (v :: vs) xs =
  (tensorRow v xs) `concatCols` (tensorProductAny vs xs)

export
printComplex : Complex Double -> String
printComplex (x :+ y) =
  if y == 0 then show x
            else if x == 0 then show y ++ "i"
                 else show x ++ " + " ++ show y ++ "i"

export
printVector : Vector n -> String
printVector v = "[" ++ printVector' v ++ "]" where
  printVector' : Vector m -> String
  printVector' [] = ""
  printVector' [x] = printComplex x
  printVector' (x :: xs) = printComplex x ++ " , " ++  printVector' xs

export
printMatrix : Matrix n m -> String
printMatrix v = "[ " ++ printMat' v where
  printMat' : Matrix p q -> String
  printMat' [] = ""
  printMat' [x] = printVector x ++ " ]"
  printMat' (x :: xs) = printVector x ++ "\n  " ++ printMat' xs


------------ Lemmas about matrices ---------------------------------------

export
powPlusMultZeroRightNeutral : (n : Nat) -> plus (power 2 n) (mult 0 (power 2 n)) = power 2 n
powPlusMultZeroRightNeutral n = rewrite plusZeroRightNeutral (power 2 n) in Refl

export
multPowerPowerPlus : (base, exp, exp' : Nat) ->
                     power base (exp + exp') = (power base exp) * (power base exp')
multPowerPowerPlus base Z       exp' = 
    rewrite plusZeroRightNeutral (power base exp') in Refl
multPowerPowerPlus base (S exp) exp' =
  rewrite multPowerPowerPlus base exp exp' in
    rewrite sym $ multAssociative base (power base exp) (power base exp') in
       Refl

powerMultLemma : {i, n : Nat} -> mult (power 2 i) (power 2 (minus n i)) = power 2 (i + minus n i )
powerMultLemma {i,n} = sym $ multPowerPowerPlus 2 i (minus n i)
 
powerLTEisN : {i, n : Nat} -> LTE i n -> power 2 (i + minus n i ) = power 2 n
powerLTEisN {i,n} lte = rewrite plusCommutative i (minus n i) in rewrite plusMinusLte' i n lte in Refl

powerMultDifIsN : {i, n : Nat} -> LTE i n -> mult (power 2 i) (power 2 (minus n i)) = power 2 n
powerMultDifIsN {i,n} lte = rewrite sym $ powerLTEisN lte in rewrite powerMultLemma {i, n} in Refl

export
powPlusZeroRightNeutral : {m : Nat} -> Matrix (plus (plus (power 2 m) (plus (power 2 m) 0)) 0) 1 -> Matrix (plus (power 2 m) (plus (power 2 m) 0)) 1
powPlusZeroRightNeutral mat = rewrite sym $ plusZeroRightNeutral (plus (power 2 m) (plus (power 2 m) 0)) in mat

export
powerOneNeutral : (base : Nat) -> power base 1 = base
powerOneNeutral base = rewrite multCommutative base 1 in multOneLeftNeutral base




------------ LINEAR-ALGEBRAIC SIMULATION: MATRIX OPERATIONS ---------------



export
matrixH : Matrix 2 2
matrixH = [[(1/(sqrt 2)) :+ 0, (1/(sqrt 2)) :+ 0], [(1/(sqrt 2)) :+ 0 , (-1/(sqrt 2)) :+ 0]]

export
matrixP : Double -> Matrix 2 2
matrixP p = [[1 , 0] , [0, cis p]]

export
matrixCNOT : Matrix 4 4
matrixCNOT = [[1,0,0,0] , [0,1,0,0] , [0,0,0,1] , [0,0,1,0]]

export
matrixX : Matrix 2 2
matrixX = [[0,1] , [1,0]]

export
matrixKet0Bra0 : Matrix 2 2
matrixKet0Bra0 = [[1 :+ 0,0 :+ 0] , [0 :+ 0,0 :+ 0]]

export
matrixKet1Bra1 : Matrix 2 2
matrixKet1Bra1 = [[0 :+ 0,0 :+ 0] , [0 :+ 0,1 :+ 0]]

export
simpleTensor : Matrix 2 2 -> (n : Nat) -> Nat -> Matrix (power 2 n) (power 2 n)
simpleTensor _ 0 _ = [[1]]
simpleTensor m (S n) 0 = m `tensorProduct` (simpleTensor m n (S n))
simpleTensor m (S n) (S k) = (matrixId 2) `tensorProduct` (simpleTensor m n k)


export
toDensityRep : { n : Nat } -> Matrix (power 2 n) 1 -> Matrix (power 2 n) (power 2 n) 
toDensityRep m = matrixMult m (transposeMatrix m)

--subMatN : (k : Nat) -> Matrix (power 2 n) (power 2 n) -> Matrix 2

export
tensorCnotAux : (n : Nat) -> (control : Nat) -> (target : Nat) -> Matrix (power 2 n) (power 2 n)
tensorCnotAux 0 _ _ = [[1]]
tensorCnotAux (S n) 0 0 = (matrixId 2) `tensorProduct` (tensorCnotAux n (S n) (S n)) --should not be happening
tensorCnotAux (S n) 0 (S m) = matrixKet1Bra1 `tensorProduct` (tensorCnotAux n (S n) m)
tensorCnotAux (S n) (S k) 0 = matrixX `tensorProduct` (tensorCnotAux n k (S n))
tensorCnotAux (S n) (S k) (S m) = (matrixId 2) `tensorProduct` (tensorCnotAux n k m)

export
tensorCNOT : (n : Nat) -> (control : Nat) -> (target : Nat) -> Matrix (power 2 n) (power 2 n)
tensorCNOT nbQbits control target = (simpleTensor matrixKet0Bra0 nbQbits control) `addMatrix` (tensorCnotAux nbQbits control target)


export
tensorUpId : {n:Nat} -> {i:Nat} -> Matrix (power 2 i) (power 2 i) -> Matrix (power 2 n) (power 2 n)
tensorUpId {n} {i} mi = case decEq n i of 
  Yes prf => rewrite prf in mi
  No _ => case isLTE i n of
    Yes prf => rewrite sym $ powerMultDifIsN (prf) in mi `tensorProductAny` (matrixId (power 2 (minus n i)))
    No _ => matrixId (power 2 n)


export
tensorProductVect : Matrix (power 2 n) 1 -> Matrix (power 2 p) 1 -> Matrix (power 2 (n + p)) 1
tensorProductVect xs ys =
  rewrite multPowerPowerPlus 2 n p
  in tensorProduct xs ys

export
normState2 : Matrix n 1 -> Double
normState2 [] = 0
normState2 ([x] :: xs) = let m = magnitude x in m * m + normState2 xs


export
toTensorBasis : Matrix n 2 -> Matrix (power 2 n) 1
toTensorBasis [] = [[1]]
toTensorBasis ([x,y] :: xs) = tensorProduct [[x] , [y]] (toTensorBasis xs)

export
ket0 : (n : Nat) -> Matrix n 2
ket0 0 = []
ket0 (S k) = [1 , 0] :: ket0 k

export
ket1 : (n : Nat) -> Matrix n 2
ket1 0 = []
ket1 (S k) = [1 , 1] :: ket1 k

export
neutralIdPow : (n : Nat) -> Matrix (power 2 n) 1
neutralIdPow n = toTensorBasis (ket1 n)

export
controlUnitary : {n:Nat} -> Matrix n n -> Matrix (2*n) (2*n)
controlUnitary {n} unitaryIn = (tensorProduct matrixKet0Bra0 (matrixId n)) `addMatrix` (tensorProduct matrixKet1Bra1 (unitaryIn))

export
controlUnitaryPow : {n:Nat} -> Matrix (power 2 n) (power 2 n) -> Matrix (power 2 (S n)) (power 2 (S n))
controlUnitaryPow {n} unitaryIn = 
  let left = (tensorProduct matrixKet0Bra0 (matrixId (power 2 n))) in
    let right = (tensorProduct matrixKet1Bra1 (unitaryIn)) in
      left `addMatrix` right

public export
multipleControlledUnitary:  {n : Nat} -> (k : Nat) -> Matrix (power 2 n) (power 2 n) -> Matrix (power 2 (k + n)) (power 2 (k + n))
multipleControlledUnitary Z un = un
multipleControlledUnitary (S m) un = controlUnitaryPow $ multipleControlledUnitary m un

||| Complex conjugate for Complex Double
conjCD : Complex Double -> Complex Double
conjCD (re :+ im) = re :+ (-im)

||| Conjugate every entry of a matrix
conjugateMatrix : Matrix n m -> Matrix n m
conjugateMatrix = map (map conjCD)

||| Adjoint (a.k.a. dagger): A† = (conj A)^T
export
adjoint : {n : Nat} -> {m : Nat} -> Matrix n m -> Matrix m n
adjoint a = transposeMatrix (conjugateMatrix a)

||| Convenience alias for square matrices (unitaries)
export
daggerU : {n : Nat} -> Matrix n n -> Matrix n n
daggerU = adjoint

export
inv : Double -> Double
inv x = if x == 0 then 0 else 1/x

export
projectState : {n : Nat} -> Matrix (power 2 (S n)) 1 -> (i : Nat) -> 
               Bool -> Matrix (power 2 n) 1
projectState v 0 b =
  let (v1, v2) = splitAt (power 2 n) v in
      case b of
           True => rewrite sym $ powPlusMultZeroRightNeutral n in v2
           False => v1
projectState {n = 0} _ (S k) _ = [[1]]
projectState {n = S m} v (S k) b =
  let (v1, v2) = splitAt (power 2 (S m)) v
      v1' = projectState {n = m} v1 k b
      v2' = projectState {n = m} (powPlusZeroRightNeutral v2) k b
  in rewrite plusZeroRightNeutral (power 2 m) in v1' ++ v2'


--------------Permutation Matrix Generation --------------

|||Find the smallest missing in an ordered vector
export
smallestMissing': List Nat -> Nat
smallestMissing' [] = Z
smallestMissing' [Z] = S Z 
smallestMissing' [S k] = S (S k)
smallestMissing' (x::y::ys) = case decEq (S x) y of
       Yes _ => smallestMissing' (y::ys)
       No _ => (S x)
      
|||Find the smallest missing in an ordered vector
export
smallestMissing: List Nat -> Nat
smallestMissing [] = Z
smallestMissing [Z] = S Z 
smallestMissing [S k] = S (S k)
smallestMissing (x::y::ys) = case x of 
  Z => case decEq (S x) y of
       Yes _ => smallestMissing' (y::ys)
       No _ => (S x)
  (S k) => Z

makeNVect' : (n:Nat) -> Vect n Nat
makeNVect' Z = []
makeNVect' (S k) = k :: makeNVect' k

makeNVect : (n:Nat) -> Vect n Nat
makeNVect n = reverse $ makeNVect' n

makeNList' : (n:Nat) -> List Nat
makeNList' Z = []
makeNList' (S k) = k :: makeNList' k

makeNList : (n:Nat) ->  List Nat
makeNList n = reverse $ makeNList' n

export
vectToList : Vect i Nat -> List Nat
vectToList [] = []
vectToList (x::xs) = x :: vectToList xs

listToVect : {i:Nat} -> List Nat -> Vect i Nat 
listToVect {i = Z} [] = []
listToVect {i = Z} (x::xs) = []
listToVect {i = S k} (x::xs) = x :: listToVect xs
listToVect {i = S k} [] = makeNVect (S k)

padtoN : (n:Nat) -> List Nat -> List Nat
padtoN n [] = makeNList n
padtoN Z any = any
padtoN (S k) (x::xs) = padtoN k ((x::xs) ++ [(smallestMissing (sort (x::xs)))])

export
padtoNVect : {i:Nat} -> (n:Nat) -> Vect i Nat -> Vect n Nat
padtoNVect {i} n vect = case isLTE n i of
  Yes _ => makeNVect n -- this is vacuous for us
  No _ => let k = minus n i in 
    listToVect (padtoN k (vectToList vect))

natToComplex : Nat -> Complex Double
natToComplex n = (cast n) :+ 0.0

toNatV : Vect n Nat -> Vect n (Complex Double)
toNatV [] = []
toNatV (x::xs) = natToComplex x :: toNatV xs

--------------------------------------------------------------------------------
-- Duplication via reconstruction of linear matrices. This is helpful so that
-- a linear version of all operations above need not be defined
--------------------------------------------------------------------------------

||| Linear duplication for Complex Double.
||| Uses linear duplication for the underlying Doubles.
dupComplexDouble : (1 z : Complex Double) -> (Complex Double, Complex Double)
dupComplexDouble (x :+ y) =
  let (x1, x2) = dup x
      (y1, y2) = dup y
  in  (x1 :+ y1, x2 :+ y2)

||| Linear duplication for Vector n = Vect n (Complex Double)
dupVectCD : {n : Nat} -> (1 xs : Vector n) -> (Vector n, Vector n)
dupVectCD {n = Z}     []        = ([], [])
dupVectCD {n = S k} (x :: xs) =
  let (x1, x2)   = dupComplexDouble x
      (xs1, xs2) = dupVectCD xs
  in  (x1 :: xs1, x2 :: xs2)

  
||| Linear duplication for Matrix n m = Vect n (Vect m (Complex Double))
export
dupMatrixCD : {n,m : Nat} -> (1 mat : Matrix n m) -> (Matrix n m, Matrix n m)
dupMatrixCD {n = Z}     []        = ([], [])
dupMatrixCD {n = S k} (row :: rs) =
  let (r1, r2)   = dupVectCD row
      (rs1, rs2) = dupMatrixCD rs
  in  (r1 :: rs1, r2 :: rs2)

export
plusMinusLeft : {i : Nat} -> {n : Nat} -> LTE i n -> i + (minus n i) = n
plusMinusLeft {i = Z} {n} prf =
  rewrite plusZeroLeftNeutral n in rewrite minusZeroRight' n in Refl

plusMinusLeft {i = S i} {n = S n} (LTESucc prf) =
  cong S (plusMinusLeft prf)


-- Extract bits based on the target wires
extractSubIndex : Vect i Nat -> Nat -> Nat
extractSubIndex [] val = 0
extractSubIndex (wire :: ws) val = 
    let bit = (val `div` (power 2 wire)) `mod` 2
    in (bit * (power 2 (length ws))) + extractSubIndex ws val

-- Determine the 'residual' value of the index for bits NOT in perm
setSubIndexZero : Vect i Nat -> Nat -> Nat
setSubIndexZero [] originalVal = originalVal
setSubIndexZero (wire :: ws) originalVal = 
    let mask = power 2 wire
        -- Clear the bit at 'wire'
        cleared = (originalVal `div` (mask * 2) * (mask * 2)) + (originalVal `mod` mask)
    in setSubIndexZero ws cleared

-- Helper: Extract sub-index (Wire 0 is MSB)
extractSubIndexRev : {n : Nat} -> {i : Nat} -> Vect i Nat -> Nat -> Nat
extractSubIndexRev [] val = 0
extractSubIndexRev {n} (wire :: ws) val = 
    let bitPos = minus (minus n 1) wire
        bit = (val `div` (power 2 bitPos)) `mod` 2
    in (bit * (power 2 (length ws))) + extractSubIndexRev {n} ws val

-- Helper: Zero out specific bits to check if "spectator" qubits match
setSubIndexZeroRev : {n : Nat} -> {i : Nat} -> Vect i Nat -> Nat -> Nat
setSubIndexZeroRev [] originalVal = originalVal
setSubIndexZeroRev {n} (wire :: ws) originalVal = 
    let bitPos = minus (minus n 1) wire
        mask = power 2 bitPos
        -- Clear the bit at bitPos
        cleared = (originalVal `div` (mask * 2) * (mask * 2)) + (originalVal `mod` mask)
    in setSubIndexZeroRev {n} ws cleared

-- -----------------------
-- Nat-only Vect builders
-- -----------------------

buildVectFrom : (len : Nat) -> (start : Nat) -> (f : Nat -> a) -> Vect len a
buildVectFrom Z     _     f = []
buildVectFrom (S k) start f = f start :: buildVectFrom k (S start) f

buildMatrixNat : (rows : Nat) -> (cols : Nat) ->
                 (f : Nat -> Nat -> Complex Double) ->
                 Matrix rows cols
buildMatrixNat rows cols f =
  buildVectFrom rows 0 (\r => buildVectFrom cols 0 (\c => f r c))

-- --------------------------------
-- Nat indexing with a safe default
-- --------------------------------

indexNatDef : a -> Nat -> Vect n a -> a
indexNatDef def Z     []        = def
indexNatDef def Z     (x :: xs) = x
indexNatDef def (S k) []        = def
indexNatDef def (S k) (x :: xs) = indexNatDef def k xs

zeroRow : (m : Nat) -> Vect m (Complex Double)
zeroRow Z = []
zeroRow (S k) = 0 :: zeroRow k

matIndexNatDef : {n : Nat} -> {m : Nat} ->
                 Complex Double -> Nat -> Nat -> Matrix n m -> Complex Double
matIndexNatDef {m} def r c mat =
  let row : Vect m (Complex Double)
      row = indexNatDef (zeroRow m) r mat
  in  indexNatDef def c row
-- -----------------------
-- Bit utilities (Nat-only)
-- -----------------------

predNat : Nat -> Nat
predNat Z     = Z
predNat (S k) = k

-- bit at position p counting from LSB=0
bitAtLSB : Nat -> Nat -> Nat
bitAtLSB p x = ((x `div` (power 2 p)) `mod` 2)

-- Convention: qubit 0 is the MOST-significant qubit in the tensor order.
bitOfQubit : (n : Nat) -> (q : Nat) -> Nat -> Nat
bitOfQubit n q idx = bitAtLSB (minus (predNat n) q) idx

elemNatVect : (x : Nat) -> Vect k Nat -> Bool
elemNatVect x [] = False
elemNatVect x (y :: ys) =
  case decEq x y of
    Yes _ => True
    No  _ => elemNatVect x ys

-- Extract i-bit sub-index from an n-qubit basis index, using perm order.
extractSubIndexNew : {n : Nat} -> (perm : Vect i Nat) -> Nat -> Nat
extractSubIndexNew {n} []        idx = 0
extractSubIndexNew {n} (q :: qs) idx =
  let b  = bitOfQubit n q idx
      r  = extractSubIndexNew {n} qs idx
  in  b * (power 2 (length qs)) + r

-- Check equality on qubits NOT in perm
sameOnOtherQubits : {n : Nat} -> (perm : Vect i Nat) -> Nat -> Nat -> Bool
sameOnOtherQubits {n} perm r c = go 0 n where
  go : Nat -> Nat -> Bool
  go _ Z = True
  go q (S k) =
    if elemNatVect q perm then
      go (S q) k
    else
      if bitOfQubit n q r == bitOfQubit n q c
         then go (S q) k
         else False

-- -----------------------
-- applyUM with Nat-only indexing
-- -----------------------
export
applyUM : {n : Nat} -> {i : Nat} ->
          (perm : Vect i Nat) ->
          (ui   : Matrix (power 2 i) (power 2 i)) ->
          Matrix (power 2 n) (power 2 n)
applyUM {n} {i} perm ui =
  buildMatrixNat (power 2 n) (power 2 n) entry where

    entry : Nat -> Nat -> Complex Double
    entry r c =
      if sameOnOtherQubits {n} perm r c then
        let rr = extractSubIndexNew {n} perm r
            cc = extractSubIndexNew {n} perm c
        in  matIndexNatDef 0 rr cc ui
      else 0

