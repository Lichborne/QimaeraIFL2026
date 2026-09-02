module QuditMatrix

import Matrix
import Data.Nat
import Data.Fin
import Data.List
import Data.Linear 
import Data.Vect as V
import Decidable.Equality
import Complex
import NatRules
import UnitaryLinear

%default total

||| This development is for simulating Qudits, and is separate from the main file.

public export
QuditUM : (base : Nat) -> (n : Nat) -> Type
QuditUM base n = Matrix (power base n) (power base n)

public export
idQU : {base:Nat} -> {n:Nat} -> QuditUM base n
idQU {base} {n} = matrixId (power base n)


----------- basic helpers -----------

modNatSafe : Nat -> Nat -> Nat
modNatSafe _ Z = Z
modNatSafe x (S k) =
  let xi : Integer = cast x
      di : Integer = cast (S k)
      r  : Integer = xi `mod` di
  in cast r

divNatSafe : Nat -> Nat -> Nat
divNatSafe _ Z = Z
divNatSafe x (S k) =
  let xi : Integer = cast x
      di : Integer = cast (S k)
      q  : Integer = xi `div` di
  in cast q

powC : Complex Double -> Nat -> Complex Double
powC z Z = 1
powC z (S k) = z * powC z k

omega : Nat -> Complex Double
omega Z = 1
omega (S b) = cis (2 * pi / cast (S b))

zeroVector : (m : Nat) -> Vector m
zeroVector m = replicate m 0

zeroMatrix : (n : Nat) -> (m : Nat) -> Matrix n m
zeroMatrix n m = replicate n (zeroVector m)


||| Extract base digit of x at position p (LS digit p=0).
digitAt : (base : Nat) -> (x : Nat) -> (p : Nat) -> Nat
digitAt Z _ _ = 0
digitAt (S b) x p =
  let xi    : Integer = cast x
      denom : Integer = cast (power (S b) p)
      di    : Integer = (xi `div` denom) `mod` (cast (S b))
  in if di == 0 then 0 else cast di

||| Convention: perm[i] = old position that becomes output position i.
permuteIndexBase : {n : Nat} -> (base : Nat) -> (perm : Vect n Nat) -> (x : Nat) -> Nat
permuteIndexBase {n} base perm x = go 0 perm where
  go : Nat -> Vect k Nat -> Nat
  go _ [] = 0
  go i (oldPos :: rest) =
    let d : Nat = digitAt base x oldPos
    in d * power base i + go (S i) rest

export
permMatrixBase : {n : Nat} -> (base : Nat) -> (perm : Vect n Nat) ->
                 Matrix (power base n) (power base n)
permMatrixBase {n} base perm =
  V.Fin.tabulate $ \rFin =>
    V.Fin.tabulate $ \cFin =>
      let r  : Nat = finToNat rFin
          c  : Nat = finToNat cFin
          rp : Nat = permuteIndexBase {n} base perm c
      in case decEq r rp of
           Yes _ => 1
           No  _ => 0

||| One qubit helpers
export
basisKet1 : (base : Nat) -> (k : Nat) -> Vect base (Complex Double)
basisKet1 base k =
  V.Fin.tabulate $ \i => if finToNat i == k then 1 else 0

export
ketConst : (base : Nat) -> (q : Nat) -> (k : Nat) -> Matrix q base
ketConst _ 0 _ = []
ketConst base (S t) k = basisKet1 base k :: ketConst base t k

export
toTensorBasisBase : {q : Nat} -> (base : Nat) -> Matrix q base -> Matrix (power base q) 1
toTensorBasisBase base [] = [[1]]
toTensorBasisBase base (row :: xs) =
  tensorProduct (makeCol row) (toTensorBasisBase base xs)

export
neutralIdPowBase : (base : Nat) -> (q : Nat) -> Matrix (power base q) 1
neutralIdPowBase base q = toTensorBasisBase base (ketConst base q 0)

------------------------ projectors -----------------------------
export
projKetBra : (base : Nat) -> (c : Nat) -> Matrix base base
projKetBra base c =
  V.Fin.tabulate $ \r =>
    V.Fin.tabulate $ \k =>
      if finToNat r == c && finToNat k == c then 1 else 0


---------Qudit gates: X, Z, F(QFT), V (non-Clifford phase)---------

||| k+a mod base
export
gateXpow : (base : Nat) -> (a : Nat) -> Matrix base base
gateXpow base a =
  V.Fin.tabulate $ \r =>
    V.Fin.tabulate $ \c =>
      let rr = finToNat r
          cc = finToNat c
      in if rr == modNatSafe (cc + a) base then 1 else 0

export
gateX : (base : Nat) -> Matrix base base
gateX base = gateXpow base 1

||| Z^b
export
gateZpow : (base : Nat) -> (b : Nat) -> Matrix base base
gateZpow base b =
  let w = omega base in
  V.Fin.tabulate $ \r =>
    V.Fin.tabulate $ \c =>
      let rr = finToNat r
          cc = finToNat c
      in if rr == cc then powC w (b * cc) else 0

export
gateZ : (base : Nat) -> Matrix base base
gateZ base = gateZpow base 1

||| F : QFT over Z_base
export
gateF : (base : Nat) -> Matrix base base
gateF base =
  let w : Complex Double = omega base
      s : Complex Double =
        case base of
          Z => 0
          (S b) => ((1 / sqrt (cast (S b))) :+ 0)
  in V.Fin.tabulate $ \r =>
       V.Fin.tabulate $ \c =>
         let j = finToNat r
             k = finToNat c
         in s * powC w (j * k)
         
|||Cubic Phase
export
gateV : (base : Nat) -> Matrix base base
gateV base =
  let w = omega base in
  V.Fin.tabulate $ \r =>
    V.Fin.tabulate $ \c =>
      let rr = finToNat r
          cc = finToNat c
      in if rr == cc then powC w (cc * cc * cc) else 0

||| Pauli group helpers (generalized)
export
pauliXZ : (base : Nat) -> (a : Nat) -> (b : Nat) -> Matrix base base
pauliXZ base a b = matrixMult (gateXpow base a) (gateZpow base b)

export
pauliZX : (base : Nat) -> (a : Nat) -> (b : Nat) -> Matrix base base
pauliZX base a b = matrixMult (gateZpow base b) (gateXpow base a)

export
pauliPhase : (base : Nat) -> (t : Nat) -> Matrix base base -> Matrix base base
pauliPhase base t m = multScalarMatrix (powC (omega base) t) m

|||COVERING SUM gate (generalised CNOT), constructive
sum2Core : (base : Nat) -> Matrix (base * base) (base * base)
sum2Core base =
  let as : Vect base Nat
      as = V.Fin.tabulate finToNat

      step : Nat -> Matrix (base * base) (base * base)
      step a = tensorProductAny (projKetBra base a) (gateXpow base a)

      mats : Vect base (Matrix (base * base) (base * base))
      mats = map step as
  in foldl addMatrix (zeroMatrix (base * base) (base * base)) mats


||| Make power base 2 definitional enough for SUM lifting
powerTwoNeutral : (base : Nat) -> power base 2 = base * base
powerTwoNeutral base =
  -- power base (1+1) = power base 1 * power base 1
  rewrite multPowerPowerPlus base 1 1 in
  rewrite powerOneNeutral base in
  Refl

-- Reinterpret sum2Core as living in dimension power base 2
export
sum2CorePow : (base : Nat) -> Matrix (power base 2) (power base 2)
sum2CorePow base =
  rewrite (powerTwoNeutral base) in
    sum2Core base

--------------------------------------------------------------------------------
-- SUM_{0,1} acting on an n-qudit register (tensor identity on remaining)
--------------------------------------------------------------------------------
sum01OnN : {n : Nat} -> (base : Nat) -> Matrix (power base n) (power base n)
sum01OnN {n = Z} _ = [[1]]
sum01OnN {n = (S Z)} base = matrixId (power base (S Z))
sum01OnN {n = (S (S k))} base =
  rewrite (multPowerPowerPlus base 2 k) in
    tensorProductAny (sum2CorePow base) (matrixId (power base k))


-- build perm = [control,target,rest...] (same convention as permMatrixBase)
indices : (n : Nat) -> Vect n Nat
indices n = V.Fin.tabulate finToNat

filterOut2 : Nat -> Nat -> List Nat -> List Nat
filterOut2 a b [] = []
filterOut2 a b (x :: xs) =
  if x == a || x == b then filterOut2 a b xs else x :: filterOut2 a b xs

nthOr : Nat -> Nat -> List Nat -> Nat
nthOr def Z (x :: _) = x
nthOr def (S k) (_ :: xs) = nthOr def k xs
nthOr def _ [] = def

permBringToFront : {n : Nat} -> (control : Nat) -> (target : Nat) -> Vect n Nat
permBringToFront {n = Z} _ _ = []
permBringToFront {n = (S Z)} _ _ = [0]
permBringToFront {n = (S (S k))} control target =
  let restList : List Nat = filterOut2 control target (toList (indices (S (S k))))
      restVect : Vect k Nat = V.Fin.tabulate (\j => nthOr 0 (finToNat j) restList)
  in control :: target :: restVect

||| SUM on arbitrary wires
export
tensorSUM : {n : Nat} -> (base : Nat) -> (control : Nat) -> (target : Nat) ->
            Matrix (power base n) (power base n)
tensorSUM {n} base control target =
  case decEq control target of
    Yes _ => matrixId (power base n)
    No _ =>
      let perm : Vect n Nat = permBringToFront {n} control target
          p    : Matrix (power base n) (power base n) = permMatrixBase {n} base perm
          g01  : Matrix (power base n) (power base n) = sum01OnN {n} base
      in matrixMult (adjoint p) (matrixMult g01 p)

----------------------- multi-controlled-sum ------------------------

export
controlsMatch : (base : Nat) -> (controls : Vect k Nat) -> (val : Nat) -> (x : Nat) -> Bool
controlsMatch _ [] _ _ = True
controlsMatch base (c :: cs) val x =
  (digitAt base x c == val) && controlsMatch base cs val x

buildIndex : (base : Nat) -> (n : Nat) -> (dig : Nat -> Nat) -> Nat
buildIndex base n dig = go 0 n where
  go : Nat -> Nat -> Nat
  go _ Z = 0
  go i (S k) = dig i * power base i + go (S i) k

applySUMIndex : {n : Nat} -> (base : Nat) -> (control : Nat) -> (target : Nat) -> Nat -> Nat
applySUMIndex {n} base control target x =
  let a  = digitAt base x control
      b  = digitAt base x target
      b' = modNatSafe (a + b) base
  in buildIndex base n (\i => if i == target then b' else digitAt base x i)

export
multiControlledSUM : {n : Nat} ->
                     (base : Nat) ->
                     (controls : Vect k Nat) ->
                     (val : Nat) ->
                     (control : Nat) ->
                     (target : Nat) ->
                     Matrix (power base n) (power base n)
multiControlledSUM {n} base controls val control target =
  V.Fin.tabulate $ \rFin =>
    V.Fin.tabulate $ \cFin =>
      let r = finToNat rFin
          c = finToNat cFin
          out = if controlsMatch base controls val c
                   then applySUMIndex {n} base control target c
                   else c
      in case decEq r out of
           Yes _ => 1
           No  _ => 0

-------------------------- multi-controlled single-qubit ----------------------
uAt : (base : Nat) -> Matrix base base -> Nat -> Nat -> Complex Double
uAt base u i j =
  case (natToFin i {n=base}, natToFin j {n=base}) of
    (Just fi, Just fj) => V.index fj (V.index fi u) 
    _                  => 0

sameExcept : (base : Nat) -> (n : Nat) -> (target : Nat) -> Nat -> Nat -> Bool
sameExcept base n target x y = go 0 n where
  go : Nat -> Nat -> Bool
  go _ Z = True
  go i (S k) =
    if i == target
       then go (S i) k
       else (digitAt base x i == digitAt base y i) && go (S i) k

export
multiControlled1Q : {n : Nat} ->
                    (base : Nat) ->
                    (controls : Vect k Nat) ->
                    (val : Nat) ->
                    (target : Nat) ->
                    Matrix base base ->
                    Matrix (power base n) (power base n)
multiControlled1Q {n} base controls val target u =
  V.Fin.tabulate $ \rFin =>
    V.Fin.tabulate $ \cFin =>
      let r : Nat = finToNat rFin
          c : Nat = finToNat cFin
          active : Bool = controlsMatch base controls val c
      in if active
            then if sameExcept base n target r c
                    then uAt base u (digitAt base r target) (digitAt base c target)
                    else 0
            else case decEq r c of
                   Yes _ => 1
                   No _  => 0
-------------------------------------------------------------------------------
public export
plusMinusLeftQudit : {i : Nat} -> {n : Nat} -> LTE i n -> i + (minus n i) = n
plusMinusLeftQudit {i = Z} {n} _ =
  rewrite plusZeroLeftNeutral n in
  rewrite minusZeroRight' n in
  Refl
plusMinusLeftQudit {i = S i} {n = S n} (LTESucc prf) =
  cong S (plusMinusLeftQudit prf)

public export
digitAtBase : (base : Nat) -> (x : Nat) -> (p : Nat) -> Nat
digitAtBase Z _ _ = 0
digitAtBase (S b) x p =
  let xi    : Integer = cast x
      denom : Integer = cast (power (S b) p)
      di    : Integer = (xi `div` denom) `mod` (cast (S b))
  in if di == 0 then 0 else cast di

-------Extract sub-index for a list of wires (qudits, base-aware) ----------

public export
extractSubIndexBase : {i : Nat} -> (base : Nat) -> Vect i Nat -> Nat -> Nat
extractSubIndexBase {i = Z} _ [] _ = 0
extractSubIndexBase {i = S k} base (wire :: ws) val =
  let d = digitAtBase base val wire
  in d * power base (length ws) + extractSubIndexBase base ws val


public export
setSubIndexZeroBase : {i : Nat} -> (base : Nat) -> Vect i Nat -> Nat -> Nat
setSubIndexZeroBase {i = Z} _ [] originalVal = originalVal
setSubIndexZeroBase {i = S k} base (wire :: ws) originalVal =
  case base of
    Z => originalVal
    (S b) =>
      let bNat   : Nat = (S b)
          place  : Nat = power bNat wire
          chunk  : Nat = place * bNat
          -- remove digit at position `wire`
          high   : Nat = (originalVal `div` chunk) * chunk
          low    : Nat = originalVal `mod` place
          cleared : Nat = high + low
      in setSubIndexZeroBase bNat ws cleared

public export
buildVectFromQudit : (len : Nat) -> (start : Nat) -> (f : Nat -> a) -> Vect len a
buildVectFromQudit Z     _     _ = []
buildVectFromQudit (S k) start f = f start :: buildVectFromQudit k (S start) f

public export
buildMatrixNatQudit : (rows : Nat) -> (cols : Nat) ->
                      (f : Nat -> Nat -> Complex Double) ->
                      Matrix.Matrix rows cols
buildMatrixNatQudit rows cols f =
  buildVectFromQudit rows 0 (\r => buildVectFromQudit cols 0 (\c => f r c))

public export
indexNatDefQudit : a -> Nat -> Vect n a -> a
indexNatDefQudit def Z     []        = def
indexNatDefQudit _   Z     (x :: _)  = x
indexNatDefQudit def (S _) []        = def
indexNatDefQudit def (S k) (_ :: xs) = indexNatDefQudit def k xs

public export
zeroRowQudit : (m : Nat) -> Vect m (Complex Double)
zeroRowQudit Z     = []
zeroRowQudit (S k) = 0 :: zeroRowQudit k

public export
matIndexNatDefQudit : {n : Nat} -> {m : Nat} ->
                      Complex Double -> Nat -> Nat ->
                      Matrix.Matrix n m -> Complex Double
matIndexNatDefQudit {m} def r c mat =
  let row : Vect m (Complex Double)
      row = indexNatDefQudit (zeroRowQudit m) r mat
  in indexNatDefQudit def c row

public export
elemNatVectQudit : (x : Nat) -> Vect k Nat -> Bool
elemNatVectQudit _ [] = False
elemNatVectQudit x (y :: ys) =
  case decEq x y of
    Yes _ => True
    No  _ => elemNatVectQudit x ys

-------- Extract i-digit sub-index from an n-qudit basis index, using perm order ----------

public export
extractSubIndexNewBase : {n : Nat} -> {i : Nat} ->
                         (base : Nat) ->
                         (perm : Vect i Nat) ->
                         Nat -> Nat
extractSubIndexNewBase {n} {i = Z} _ [] idx = 0
extractSubIndexNewBase {n} {i = S k} base (q :: qs) idx =
  let d = digitAtBase base idx q
      r = extractSubIndexNewBase {n} base qs idx
  in d * power base (length qs) + r


public export
sameOnOtherQuditsBase : {n : Nat} -> {i : Nat} ->
                        (base : Nat) ->
                        (perm : Vect i Nat) ->
                        Nat -> Nat -> Bool
sameOnOtherQuditsBase {n} {i} base perm r c = go 0 n where
  go : Nat -> Nat -> Bool
  go _ Z = True
  go q (S k) =
    if elemNatVectQudit q perm then
      go (S q) k
    else
      if digitAtBase base r q == digitAtBase base c q
         then go (S q) k
         else False

|||apply a small i-qudit unitary onto an n-qudit register
||| on the wires listed in `perm` (same idea as Matrix.applyUM for qubits).
public export
applyUMBase : {n : Nat} -> {i : Nat} ->
              (base : Nat) ->
              (perm : Vect i Nat) ->
              (ui   : Matrix.Matrix (power base i) (power base i)) ->
              Matrix.Matrix (power base n) (power base n)
applyUMBase {n} {i} base perm ui =
  buildMatrixNatQudit (power base n) (power base n) entry where

    entry : Nat -> Nat -> Complex Double
    entry r c =
      if sameOnOtherQuditsBase {n} base perm r c then
        let rr = extractSubIndexNewBase {n} base perm r
            cc = extractSubIndexNewBase {n} base perm c
        in  matIndexNatDefQudit 0 rr cc ui
      else 0


public export
phaseOn1 : (base : Nat) -> Double -> Matrix base base
phaseOn1 Z _ = []
phaseOn1 (S Z) _ = [[1]]               -- base = 1, only |0>
phaseOn1 (S (S k)) p =
  V.Fin.tabulate $ \r =>
    V.Fin.tabulate $ \c =>
      let rr = finToNat r
          cc = finToNat c
      in if rr == cc then
            if rr == 1 then cis p else 1
         else 0

public export
asPow1 : (base : Nat) -> Matrix base base -> Matrix (power base 1) (power base 1)
asPow1 base m = rewrite multOneRightNeutral base in m

|||Unitary conversion
public export
unitaryToQuditUM : {n : Nat} -> (base : Nat) -> Unitary n -> QuditUM base n
unitaryToQuditUM {n} base IdGate = idQU {base} {n}

unitaryToQuditUM {n} base (H j u) =
  let g1 : Matrix (power base 1) (power base 1)
      g1 = asPow1 base (gateF base)

      g : QuditUM base n
      g = applyUMBase {n} {i = 1} base [j] g1
  in matrixMult g (unitaryToQuditUM {n} base u)

unitaryToQuditUM {n} base (P p j u) =
  let g1 : Matrix (power base 1) (power base 1)
      g1 = asPow1 base (phaseOn1 base p)

      g : QuditUM base n
      g = applyUMBase {n} {i = 1} base [j] g1
  in matrixMult g (unitaryToQuditUM {n} base u)

unitaryToQuditUM {n} base (CNOT c t u) =
  let g2 : Matrix (power base 2) (power base 2)
      g2 = sum2CorePow base

      g : QuditUM base n
      g = applyUMBase {n} {i = 2} base [c, t] g2
  in matrixMult g (unitaryToQuditUM {n} base u)