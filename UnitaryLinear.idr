module UnitaryLinear

import Data.Vect
import Data.Nat
import System.File
import Injection
import Lemmas

import LinearTypes

infixr 9 .
infixr 10 #

%default total

------------------------Local Lemmas --------------------------
export 
ltToLTE : {left,right:Nat} -> LTE (S left) right = LT left right 
ltToLTE = Refl

------------------------Unitaries (Linear) -----------------------

public export
data Unitary : Nat -> Type where
  IdGate : Unitary n
  H      : (j : Nat) -> {auto prf : LT j n} -> (1 _ : Unitary n) -> Unitary n
  P      : (p : Double) -> (j : Nat) -> {auto prf : LT j n} -> (1 _ : Unitary n) -> Unitary n
  CNOT   : (c : Nat) -> (t : Nat) -> 
            {auto prf1 : LT c n} -> {auto prf2 : LT t n} -> {auto prf3 :  Either (LT c t) (LT t c) } -> 
            (1 _ : Unitary n) -> Unitary n

------------------------consumption Utility---------------------
||| Consume a linear unitary (used in case application fails)
export
consumeU : (1_ : Unitary n) -> ()
consumeU IdGate = ()
consumeU (H j g  ) = consumeU g 
consumeU (P p j g ) = consumeU g 
consumeU (CNOT c t g) = consumeU g

-------------------------------APPLY---------------------------
|||Apply a smaller circuit of size i to a bigger one of size n
|||The vector of wires on which we apply the circuit must follow some constraints:
|||All the indices must be smaller than n, and they must be all different
public export
apply : {i : Nat} -> {n : Nat} -> 
        (1 _ : Unitary i) -> (1 _ : Unitary n) -> 
        (v : Vect i Nat) -> 
        {auto prf : (IsInjectiveT n v)} -> 
        Unitary n
apply IdGate g2 _ = g2
apply (H j g1) g2 v = 
  let prf1 = indexInjectiveVect j n v {prf} 
  in H (indexLT j v) {prf = prf1} (apply g1 g2 v)
apply (P p j g1) g2 v = 
  let prf1 = indexInjectiveVect j n v {prf}
  in P p (indexLT j v) {prf = prf1} (apply g1 g2 v)
apply {i} {n} (CNOT c t {prf1} {prf2} {prf3} g1) g2 v = 
  let prf4 = indexInjectiveVect c n v {prf = prf}
      prf5 = indexInjectiveVect t n v {prf = prf}
      prf6 = differentIndexInjectiveVect c t n {prf1 = prf3} v {prf2 = prf} {prf3 = prf1} {prf4 = prf2}
  in CNOT (indexLT c v) (indexLT t v) {prf1 = prf4} {prf2 = prf5} {prf3 = prf6} (apply g1 g2 v)

---------------------------COMPOSE-----------------------------
|||Compose 2 circuits of the same size
public export
compose : (1 _ : Unitary n) -> (1 _ : Unitary n) -> Unitary n
compose IdGate g1 = g1
compose (H j g1) g2 = H j (compose g1 g2)
compose (P p j g1) g2 = P p j (compose g1 g2)
compose (CNOT c t g1) g2 = CNOT c t (compose g1 g2)

export
composeN : {n:Nat} -> (1 _ : Unitary n) -> (1 _ : Unitary n) -> Unitary n
composeN IdGate g1 = g1
composeN (H j g1) g2 = H j (compose g1 g2)
composeN (P p j g1) g2 = P p j (compose g1 g2)
composeN (CNOT c t g1) g2 = CNOT c t (compose g1 g2)

public export
(.) : (1 _ : Unitary n) -> (1 _ : Unitary n) -> Unitary n
(.) = compose 

---------------------------ADJOINT-----------------------------
|||Find the adjoint of a circuit
public export
adjoint : Unitary n -> Unitary n
adjoint IdGate = IdGate
adjoint (H j g) = (adjoint g) . (H j IdGate)
adjoint (P p j g) = (adjoint g) . (P (-p) j IdGate)
adjoint (CNOT c t g) = (adjoint g) . (CNOT c t IdGate)


---------------------TENSOR PRODUCT----------------------------
|||Make the tensor product of two circuits
public export
tensor : {n : Nat} -> {p : Nat} -> (1 _ : Unitary n) -> ( 1 _ : Unitary p) -> Unitary (n + p)
tensor g1 g2 = 
  let p1 = allSmallerRangeVect 0 n
      p2 = isInjectiveRangeVect n p
      p3 = allSmallerPlus n p (rangeVect 0 n) p1 
      p4 = IsInjectiveSucc (allDiffRangeVect 0 n) p3
  in apply {i = p} {n = n + p} g2 (apply {i=n} {n = n+p} g1 (IdGate {n = n+p}) (rangeVect 0 n) {prf = p4}) (rangeVect n p) {prf = p2}

public export
(#) : {n : Nat} -> {p : Nat} -> (1 _ : Unitary n) -> (1 _ : Unitary p) -> Unitary (n + p)
(#) = tensor

----------------------CLASSICAL GATES--------------------------
public export
HGate : Unitary 1
HGate = H 0 IdGate

public export
PGate : Double -> Unitary 1
PGate r = P r 0 IdGate

public export
CNOTGate : Unitary 2
CNOTGate = CNOT 0 1 IdGate

public export
T : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
T j g = P (pi/4) j {prf} g

public export
TGate : Unitary 1
TGate = T 0 IdGate

public export
TAdj : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
TAdj j g = P (-pi/4) j {prf} g

public export
TAdjGate : Unitary 1
TAdjGate = TAdj 0 IdGate

public export
S : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
S j g = P (pi/2) j {prf} g

public export
SGate : Unitary 1
SGate = S 0 IdGate

public export
SAdj : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
SAdj j g = P (-pi/2) j {prf} g

public export
SAdjGate : Unitary 1
SAdjGate = SAdj 0 IdGate

public export
Z : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
Z j g = P pi j {prf} g

public export
ZGate : Unitary 1
ZGate = Z 0 IdGate

public export
X : (j : Nat) -> {auto prf : LT j n} -> Unitary n -> Unitary n
X j g = H j (Z j (H j g))

public export
XGate : Unitary 1
XGate = X 0 IdGate

public export
RxGate : Double -> Unitary 1
RxGate p = HGate . PGate p . HGate

public export
RyGate : Double -> Unitary 1
RyGate p = SAdjGate . HGate . PGate (-p) . HGate . SGate

public export
RzGate : Double -> Unitary 1
RzGate p = PGate p 

public export
CX : (n: Nat) -> (m: Nat) -> {auto prf : LT n m} -> {auto prf2: LT 0 n} -> Unitary m
CX _ 0 {prf} = absurd prf
CX 0 (S l) {prf} {prf2} = absurd prf2 
CX (S k) (S l) = (CNOT 0 (S k) (IdGate))

public export
RZCX : (gamma: Double) -> {n:Nat} -> {m:Nat} -> {auto prf : LT n m} -> {auto prf2: LT 0 n} -> Unitary m
RZCX g {n} {m} = (P g n (CX n m))


---------------------CONTROLLED VERSIONS-----------------------
|||Toffoli gate
public export
toffoli : Unitary 3
toffoli = 
  let g1 = CNOT 1 2 (H 2 IdGate)
      g2 = CNOT 0 2 (TAdj 2 g1)
      g3 = CNOT 1 2 (T 2 g2)
      g4 = CNOT 0 2 (TAdj 2 g3)
      g5 = CNOT 0 1 (T 1 (H 2 (T 2 g4)))
  in CNOT 0 1 (T 0 (TAdj 1 g5))

|||Controlled Hadamard gate
public export
controlledH : Unitary 2
controlledH =
  let h1 = (IdGate {n=1}) # (SAdjGate . HGate . TGate . HGate . SGate)
      h2 = (IdGate {n=1}) # (SAdjGate . HGate . TAdjGate . HGate . SGate)
  in h1 . CNOTGate . h2

|||Controlled phase gate
public export
controlledP : Double -> Unitary 2
controlledP p =
  let u1 = CNOT 0 1 (P (p/2) 1 IdGate)
      u2 = CNOT 0 1 (P (-p/2) 1 u1)
  in  P (p/2) 0 u2

|||Make the controlled version of a gate
public export
controlled : {n : Nat} -> (1 _ :Unitary n) -> Unitary (S n)
controlled IdGate = IdGate
controlled (H j g) = 
  let p = lemmaControlledInj n j 
  in apply {i = 2} {n = S n} controlledH (controlled g) [0, S j] {prf = p}
controlled (P p j g) = 
  let p1 = lemmaControlledInj n j
  in apply {i = 2} {n = S n} (controlledP p) (controlled g) [0, S j] {prf = p1}
controlled (CNOT c t g) = 
  let p = lemmaControlledInj2 n c t
  in apply {i = 3} {n = S n} toffoli (controlled g) [0, S c, S t] {prf = p}


public export
multipleControlled:  {n : Nat} -> (k : Nat) -> (1 _ :Unitary n) -> Unitary (k + n)
multipleControlled Z un = un
multipleControlled (S m) un = controlled $ multipleControlled m un

------------SOME USEFUL FUNCTIONS FOR CREATING GATES-----------

|||Make n tensor products of the same unitary of size 1
public export
tensorn : (n : Nat) -> Unitary 1 -> Unitary n
tensorn 0 _ = IdGate
tensorn (S k) g = g # (tensorn k g)

|||Controls on the n-1 first qubits, target on the last
public export
generalizedToffoli : (n : Nat) -> Unitary n
generalizedToffoli 0 = IdGate
generalizedToffoli 1 = IdGate
generalizedToffoli 2 = CNOT 0 1 IdGate
generalizedToffoli (S k) = controlled (generalizedToffoli k)

||| Tensor product of a Vector of Unitary operators
export
tensorMap : {n : Nat} -> {m : Nat} -> (gates : Vect n (Unitary m)) -> Unitary (n*m)
tensorMap [] = IdGate
tensorMap (gate :: gates) = gate # (tensorMap gates)

||| Tensor product of a Vector of single-qubit Unitary operators
export
tensorMapSimple : {n : Nat} -> (gates : Vect n (Unitary 1)) -> Unitary n
tensorMapSimple g = rewrite sym $ multOneRightNeutral n in tensorMap g

---------------------------------------------------------------
-- count the total number of atomic gates in a unitary circuit
export
gateCount : Unitary n -> Nat
gateCount IdGate = 0
gateCount (H j x) = S (gateCount x)
gateCount (P p j x) = S (gateCount x)
gateCount (CNOT c t x) = S (gateCount x)

--count the number of H gates in a unitary circuit
export
Hcount : Unitary n -> Nat
Hcount IdGate = 0
Hcount (H j x) = S (Hcount x)
Hcount (P p j x) = Hcount x
Hcount (CNOT c t x) = Hcount x

--count the number of P gates in a unitary circuit
export
Pcount : Unitary n -> Nat
Pcount IdGate = 0
Pcount (H j x) = Pcount x
Pcount (P p j x) = S (Pcount x)
Pcount (CNOT c t x) = Pcount x


--count the number of CNOT gates in a unitary circuit
export
CNOTcount : Unitary n -> Nat
CNOTcount IdGate = 0
CNOTcount (H j x) = CNOTcount x
CNOTcount (P p j x) = CNOTcount x
CNOTcount (CNOT c t x) = S (CNOTcount x)

----------------------------DEPTH------------------------------
|||Compute the depth of  circuit

addDepth : Nat -> (j : Nat) -> Vect n Nat -> {auto prf : LT j n} -> Vect n Nat
addDepth j 0 (x :: xs) = j :: xs
addDepth j (S k) (x :: xs) = x :: addDepth j k xs {prf = fromLteSucc prf}

findValue : (j : Nat) -> Vect n Nat -> {auto prf : LT j n} -> Nat
findValue 0 (x::xs) = x
findValue (S k) (x::xs) = findValue k xs {prf = fromLteSucc prf}

depth' : {n : Nat} -> Unitary n -> Vect n Nat
depth' IdGate = replicate n 0
depth' (H j x) =
  let v = depth' x 
      k = findValue j v
  in addDepth (S k) j v
depth' (P p j x) = 
  let v = depth' x
      k = findValue j v
  in addDepth (S k) j v
depth' (CNOT c t x) = 
  let v = depth' x 
      k = findValue c v
      m = findValue t v
  in if k < m then
              let w = addDepth (S m) c v
              in addDepth (S m) t w
     else
              let w = addDepth (S k) c v
              in addDepth (S k) t w

export
depth : {n : Nat} -> Unitary n -> Nat
depth g = 
  let v = depth' g 
  in foldl max 0 v

----------------------------SHOW-------------------------------
|||For printing the phase gate (used for show, export to Qiskit and draw in the terminal)
|||printPhase : phase -> precision -> string for pi -> String
private
printPhase : Double -> Double -> String -> String
printPhase x epsilon s =
  if x >= pi - epsilon && x <= pi + epsilon then s
  else if x >= pi/2 - epsilon && x <= pi/2 + epsilon then s ++ "/2"
  else if x >= pi/3 - epsilon && x <= pi/3 + epsilon then s ++ "/3"
  else if x >= pi/4 - epsilon && x <= pi/4 + epsilon then s ++ "/4"
  else if x >= pi/6 - epsilon && x <= pi/6 + epsilon then s ++ "/6"
  else if x >= pi/8 - epsilon && x <= pi/8 + epsilon then s ++ "/8"
  else if x >= -pi - epsilon && x <= -pi + epsilon then "-" ++ s
  else if x >= -pi/2 - epsilon && x <= -pi/2 + epsilon then "-" ++ s ++ "/2"
  else if x >= -pi/3 - epsilon && x <= -pi/3 + epsilon then "-" ++ s ++ "/3"
  else if x >= -pi/4 - epsilon && x <= -pi/4 + epsilon then "-" ++ s ++ "/4"
  else if x >= -pi/6 - epsilon && x <= -pi/6 + epsilon then "-" ++ s ++ "/6"
  else if x >= -pi/8 - epsilon && x <= -pi/8 + epsilon then "-" ++ s ++ "/8"
  else show x

public export
Show (Unitary n) where
  show IdGate = ""
  show (H j x) = "(H " ++ show j ++ ") " ++ show x 
  show (P p j x) = "(P " ++ printPhase p 0.001 "π" ++ " " ++ show j ++ ") " ++ show x
  show (CNOT c t x) = "(CNOT " ++ show c ++ " " ++ show t ++ ") " ++ show x

------------------------- Application with IO ----------------------------

|||Safe application; if the proof is derived, it proceeds as intended, if the proof is impossible,
||| it outputs an error message and returns the larger unitary unchanged.
||| In actual use (concrete implementations), the failure cases are unreachable, but would at least
||| give warning if something when horribly wrong
public export
applySafe : {i : Nat} -> {n : Nat} -> 
        (1 _ : Unitary i) -> (1 _ : Unitary n) -> 
        (v : Vect i Nat) -> 
        LFstPair (Unitary n) (IO ())
applySafe IdGate g2 _ = g2 # pure ()
applySafe (H j g1) g2 v = case decInj n v of 
  Yes prf => let prf1 = indexInjectiveVect j n v {prf} in H (indexLT j v) {prf = prf1} (apply g1 g2 v) # pure ()
  No contra => let () = consumeU g1 in ((#) g2 ((putStrLn ("Application at " ++ show v ++ " not possible.")) >>= (\_ => pure ())))
applySafe (P p j g1) g2 v = case decInj n v of 
  Yes prf => let prf1 = indexInjectiveVect j n v {prf} in P p (indexLT j v) {prf = prf1} (apply g1 g2 v) # pure ()
  No contra => let () = consumeU g1 in ((#) g2 ((putStrLn ("Application at " ++ show v ++ " not possible.")) >>= (\_ => pure ())))
applySafe {i} {n} (CNOT c t {prf1} {prf2} {prf3} g1) g2 v = case decInj n v of 
  Yes prf => let prf4 = indexInjectiveVect c n v {prf = prf}
                 prf5 = indexInjectiveVect t n v {prf = prf}
                 prf6 = differentIndexInjectiveVect c t n {prf1 = prf3} v {prf2 = prf} {prf3 = prf1} {prf4 = prf2}
                 in CNOT (indexLT c v) (indexLT t v) {prf1 = prf4} {prf2 = prf5} {prf3 = prf6} (apply g1 g2 v) # pure ()
  No contra => let () = consumeU g1 in ((#) g2 ((putStrLn ("Application at " ++ show v ++ " not possible.")) >>= (\_ => pure ())))
  

-----------------DRAW CIRCUITS IN THE TERMINAL-----------------

private
newWireQVect : (n : Nat) -> Vect n String
newWireQVect Z = []
newWireQVect (S k) = "" :: newWireQVect k

private
addSymbol : Nat -> Bool -> (String, String) -> Vect n String -> Vect n String
addSymbol _ _ _ [] = []
addSymbol 0 False (s1, s2) (x :: xs) = (x ++ s1) :: addSymbol 0 True  (s1, s2) xs
addSymbol 0 True  (s1, s2) (x :: xs) = (x ++ s2) :: addSymbol 0 True  (s1, s2) xs
addSymbol (S k) _ (s1, s2) (x :: xs) = (x ++ s2) :: addSymbol k False (s1, s2) xs

private
addSymbolCNOT : (Nat, Nat) -> Bool -> Bool -> Vect n String -> Vect n String
addSymbolCNOT _ _ _ [] = []
addSymbolCNOT (0,0)    False b (x :: xs) = (x ++ "- • -") :: addSymbolCNOT (0, 0) True b xs
addSymbolCNOT (0, S k) False b (x :: xs) = (x ++ "- • -") :: addSymbolCNOT (0, k) True b xs
addSymbolCNOT (0, 0)   b False (x :: xs) = (x ++ "- Θ -") :: addSymbolCNOT (0, 0) b True xs
addSymbolCNOT (S k, 0) b False (x :: xs) = (x ++ "- Θ -") :: addSymbolCNOT (k, 0) b True xs
addSymbolCNOT (0, 0) True True (x :: xs) = (x ++ "-----") :: addSymbolCNOT (0, 0) True True xs
addSymbolCNOT (S j, S k) _ _   (x :: xs) = (x ++ "-----") :: addSymbolCNOT (j, k) False False xs
addSymbolCNOT (0, S k) True _  (x :: xs) = (x ++ "--|--") :: addSymbolCNOT (0, k) True False xs
addSymbolCNOT (S k, 0) _ True  (x :: xs) = (x ++ "--|--") :: addSymbolCNOT (k, 0) False True xs

private
drawWirePhase : Nat -> String
drawWirePhase 0 = ""
drawWirePhase (S n) = "-" ++ drawWirePhase n

private
drawGate : {n : Nat} -> Unitary n -> Vect n String
drawGate {n} IdGate = newWireQVect n
drawGate (H i g) = addSymbol i False ("- H -", "-----") (drawGate g)
drawGate (P p i g) =
  let epsilon = 0.001 in
  if pi/4 - epsilon <= p && pi/4 + epsilon >= p
    then addSymbol i False ("- T -", "-----") (drawGate g)
  else if -pi/4 - epsilon <= p && -pi/4 + epsilon >= p
    then addSymbol i False ("- T+ -", "------") (drawGate g)
  else if pi/2 - epsilon <= p && pi/2 + epsilon >= p
    then addSymbol i False ("- S -", "-----") (drawGate g)
  else if -pi/2 - epsilon <= p && -pi/2 + epsilon >= p
    then addSymbol i False ("- S+ -", "------") (drawGate g)
  else if pi - epsilon <= p && pi + epsilon >= p
    then addSymbol i False ("- Z -", "-----") (drawGate g)
  else let s = printPhase p epsilon "π"
  in addSymbol i False ("- P(" ++ s ++ ") -", drawWirePhase (length s + 7)) (drawGate g)
drawGate (CNOT i j g) = addSymbolCNOT (i,j) False False (drawGate g)


private
drawVect : Vect n String -> String
drawVect [] = ""
drawVect (x :: xs) = x ++ "\n" ++ drawVect xs

|||Draw a circuit in the terminal
public export
draw : {n : Nat} ->  Unitary n -> IO ()
draw g =
  let vs1 = drawGate {n} g in
  let s = drawVect vs1 in
  putStrLn s

-------------Circuit Visualization  --------------

public export
data CircVis : Nat -> Type where
  IdCirc : CircVis n
  U      : {n :Nat} -> {i :Nat} -> (at: List Nat) -> (name:String) -> (1_: Unitary i) -> (1 _ : CircVis n) -> CircVis n


||| Safety concerns us less here - we ar enot passing proofs]
public export
reindexVis : {i:Nat} -> List Nat -> Vect i Nat -> List Nat 
reindexVis [] _ = []
reindexVis _ [] = []
reindexVis {i} (x::xs) v = case isLTE (S x) i of 
  Yes prf => (indexLT x v) :: reindexVis xs v
  No _ => x ::reindexVis xs v


public export
applyVis : {i : Nat} -> {n : Nat} -> 
        (1 _ : CircVis i) -> (1 _ : CircVis n) -> 
        (v : Vect i Nat) -> 
        CircVis n
applyVis {n} IdCirc circ v = circ
applyVis (U xs s1 ui ci) circ2 v = let newXs = reindexVis xs v in
  U newXs s1 ui (applyVis ci circ2 v)

public export
tensorVis : {n : Nat} -> {p : Nat} -> (1 _ : CircVis n) -> ( 1 _ : CircVis p) -> CircVis (n + p)
tensorVis g1 g2 = applyVis {i = p} {n = n + p} g2 (applyVis {i=n} {n = n+p} g1 (IdCirc {n = n+p}) (rangeVect 0 n)) (rangeVect n p) 

|||Compose 2 circuits of the same size
public export
composeVis : (1 _ : CircVis n) -> (1 _ : CircVis n) -> CircVis n
composeVis IdCirc g1 = g1
composeVis (U xs str un circ1) circ2 = U xs str un (composeVis circ1 circ2) 

export
adjointVis : {n:Nat} ->  CircVis n -> CircVis n
adjointVis IdCirc = IdCirc
adjointVis {n} (U xs str un circ1) = composeVis (adjointVis (circ1)) (U xs str (adjoint un) (IdCirc))

public export
idUpVis :  {m:Nat} -> (1 _ : CircVis m) -> (q : Nat) -> CircVis (m + q)
idUpVis um Z = rewrite plusZeroRightNeutral m in um
idUpVis um (S k) = tensorVis um (IdCirc {n = (S k)})

||| make a neutral (0 to n) qubit vector
private
makeNeutralList' : (n:Nat) -> List Nat
makeNeutralList' Z = []
makeNeutralList' (S k) = ( k) ::makeNeutralList' k

||| make a basic vector (basically newqubitspointers n but only for vect)
export
makeNeutralList : (n:Nat) -> List Nat
makeNeutralList k = reverse $ makeNeutralList' k

export
toCircVis : {n : Nat} -> {default "U" name: String} -> Unitary n -> CircVis n
toCircVis {name} ui = U (makeNeutralList n) (name) ui IdCirc

flipIdxWrtMax : (maxN : Nat) -> List Nat -> List Nat
flipIdxWrtMax Z      xs = xs
flipIdxWrtMax (S k)  xs =
  map (\i => if i <= k then (k `minus` i) else i) xs

public export
listToVectPad : (i : Nat) -> List Nat -> Vect i Nat
listToVectPad i xs = go 0 i xs
  where
    go : Nat -> (m : Nat) -> List Nat -> Vect m Nat
    go c Z      _         = []
    go c (S m)  (x :: xs) = x :: go (S c) m xs
    go c (S m)  []        = c :: go (S c) m []

export
collapse : {n:Nat} -> (1_: CircVis n ) -> Unitary n
collapse {n} (IdCirc) = IdGate
collapse {n} (U {i} list name ui IdCirc) = let un # _ = applySafe ui (IdGate {n = n}) (listToVectPad i list) in un
collapse {n} (U {i} list name ui circ) = let un # _ = applySafe ui (collapse circ) (listToVectPad i list) in un

export
toControlled : {n:Nat} -> (k:Nat) -> Vect k Nat -> Vect n Nat -> CircVis n -> CircVis (n+k)
toControlled k controls targets (U list name ui IdCirc) = U (toList controls ++ toList targets) name (multipleControlled k ui) IdCirc
toControlled {n} k controls targets circ = let unew = collapse circ in
  U (toList controls ++ toList targets) ("C-U") (multipleControlled k unew) (IdCirc {n = n+k})

export
toControlledN : {n :Nat} -> {i :Nat} -> {p :Nat} -> (k:Nat) -> (cs: Vect i Nat) -> (ts: Vect p Nat) -> 
                (CircVis n) -> CircVis (k)
toControlledN k any1 any2 IdCirc = IdCirc
toControlledN k controls targets (U list name ui IdCirc) = U (toList controls ++ toList targets) name (multipleControlled i ui) IdCirc
toControlledN {n} k controls targets circ = U (toList controls ++ toList targets) ("C-U") (multipleControlled i (collapse circ)) (IdCirc {n = k})

-----------------DRAW CircVis IN THE TERMINAL-----------------

private
repChar : (k : Nat) -> Char -> String
repChar Z _ = ""
repChar (S k) c = strCons c (repChar k c)

private
padRightWith : (w : Nat) -> Char -> String -> String
padRightWith w c s =
  let ls = length s in
  if ls >= w then s else s ++ repChar (minus w ls) c

private
wireSeg : Nat -> String
wireSeg w = repChar w '-'

private
vertSeg : Nat -> String
vertSeg w =
  -- Minimum usable is 5: "--|--"
  if w <= 5 then "--|--"
  else "--|--" ++ repChar (minus w 5) '-'

private
gateSeg : Nat -> String -> String
gateSeg w name =
  let core = "- " ++ name ++ " -" in
  padRightWith w '-' core

private
elemNat : Nat -> List Nat -> Bool
elemNat _ [] = False
elemNat x (y :: ys) = if x == y then True else elemNat x ys

private
minNatList : Nat -> List Nat -> Nat
minNatList m [] = m
minNatList m (x :: xs) = minNatList (min m x) xs

private
maxNatList : Nat -> List Nat -> Nat
maxNatList m [] = m
maxNatList m (x :: xs) = maxNatList (max m x) xs

-- Adds a named gate at the wires in `at`.
-- If `at` has multiple indices, we draw a vertical connector from min..max.
private
addNamedAt : {n : Nat} -> (at : List Nat) -> (name : String) -> Vect n String -> Vect n String
addNamedAt [] _ vs = vs
addNamedAt (a :: as) name vs =
  let top    = minNatList a as
      bottom = maxNatList a as
      w0     = length ("- " ++ name ++ " -")
      w      = max 5 w0
      gSeg   = gateSeg w name
      wSeg   = wireSeg w
      vSeg   = gateSeg w name
  in go 0 top bottom gSeg wSeg vSeg vs
  where
    go : {n:Nat} -> (idx : Nat) -> Nat -> Nat -> String -> String -> String -> Vect n String -> Vect n String
    go {n = 0} _ _ _ _ _ _ [] = []
    go idx top bottom gSeg wSeg vSeg (x :: xs) =
      let seg =
            if idx == top then gSeg
            else if (top <= idx) && (idx <= bottom) then vSeg
            else wSeg
      in (x ++ seg) :: go (S idx) top bottom gSeg wSeg vSeg xs

private
drawCircGate : (n : Nat) -> CircVis n -> Vect n String
drawCircGate n IdCirc = newWireQVect n
drawCircGate n (U {i} at name _ g) =
  addNamedAt {n} at name (drawCircGate n g)

private
maxNat : Nat -> Nat -> Nat
maxNat x y = if x < y then y else x

private
maxList : Nat -> List Nat -> Nat
maxList acc [] = acc
maxList acc (x :: xs) = maxList (maxNat acc x) xs

public export
largestIndex : {n:Nat} -> CircVis n -> Nat
largestIndex {n} IdCirc = n
largestIndex (U at _ _ rest) =
  maxNat (maxList 0 at) (largestIndex rest)
  
dimensionForce : (m:Nat) -> CircVis n -> CircVis m
dimensionForce m IdCirc = IdCirc {n = m}
dimensionForce m (U at str ui circ) = (U at str ui (dimensionForce m circ))

||| Draw a CircVis circuit in the terminal
public export
drawCirc : {n : Nat} -> CircVis n -> IO ()
drawCirc {n} c = let vs = drawCircGate n c in putStrLn (drawVect vs) --let m = largestIndex c in let vs = drawCircGate m (dimensionForce m c) in putStrLn (drawVect vs)

--------------------------EXPORT TO QISKIT---------------------

public export
unitarytoQiskit : Unitary n -> String
unitarytoQiskit IdGate = ""
unitarytoQiskit (H i g) = unitarytoQiskit g ++  "qc.h(qr[" ++ show i ++ "])\nqc.barrier(qr)\n"
unitarytoQiskit (P p i g) = unitarytoQiskit g ++ "qc.p(" ++ printPhase p 0.001 "np.pi" ++ ", qr[" ++ show i ++ "])\nqc.barrier(qr)\n" 
unitarytoQiskit (CNOT c t g) = unitarytoQiskit g ++ "qc.cx(qr[" ++ show c ++ "], qr[" ++ show t ++ "])\nqc.barrier(qr)\n" 


private
toQiskit : {n : Nat} -> Unitary n -> String
toQiskit g =
  let s = unitarytoQiskit g in
  ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n" ++
  "from qiskit import QuantumRegister\n" ++
  "qr = QuantumRegister(" ++ show n ++ ")\n" ++
  "qc = QuantumCircuit(qr)\n\n" ++ s ++
  "\nprint(qc)")

|||Export a circuit to Qiskit code
public export
exportToQiskit : {n : Nat} -> String -> Unitary n -> IO ()
exportToQiskit str g =
  let s = toQiskit g in
      do
        a <- writeFile str s
        case a of
             Left e1 => putStrLn "Error when writing file"
             Right io1 => pure ()

private
toQiskitWithSize : {n : Nat} -> (size: Nat) -> Unitary n -> String
toQiskitWithSize sz g =
  let s = unitarytoQiskit g in
  ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n" ++
  "from qiskit import QuantumRegister\n" ++
  "qr = QuantumRegister(" ++ show sz ++ ")\n" ++
  "qc = QuantumCircuit(qr)\n\n" ++ s ++
  "\nqc.draw('mpl')")

|||Export a circuit to Qiskit code
public export
exportToQiskitWithSize : {n : Nat} -> String -> (size: Nat) -> Unitary n -> IO ()
exportToQiskitWithSize str sz g =
  let s = toQiskitWithSize sz g in
      do
        a <- writeFile str s
        case a of
             Left e1 => putStrLn "Error when writing file"
             Right io1 => pure ()


------------------ Export to Qiskit for Visualization ---------------------

public export
unitarytoQVis : Unitary n -> String
unitarytoQVis IdGate = ""
unitarytoQVis (H i g) = unitarytoQVis g ++  "\tcircuit.h(" ++ show i ++ ")\n\tcircuit.barrier()\n"
unitarytoQVis (P p i g) = unitarytoQVis g ++ "\tcircuit.p(" ++ printPhase p 0.001 "np.pi" ++ ", "++ show i ++ ")\n\tcircuit.barrier()\n" 
unitarytoQVis (CNOT c t g) = unitarytoQVis g ++ "\tcircuit.cx(" ++ show c ++ ", " ++ show t ++ ")\n\tcircuit.barrier()\n" 


private
toQVis : {n : Nat} -> Unitary n -> String
toQVis g =
  let s = unitarytoQVis g in
  ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n" ++
  "def OutputCircuit():  \n" ++
  "\tcircuit = QuantumCircuit(" ++ show n ++ ")\n" ++ s ++
  "\treturn circuit \n\nqc = OutputCircuit()")

|||Export a circuit to Qiskit code
public export
exportForQVis : {n : Nat} -> String -> Unitary n -> IO ()
exportForQVis str g =
  let s = toQVis g in
      do
        a <- writeFile str s
        case a of
             Left e1 => putStrLn "Error when writing file"
             Right io1 => pure ()
            

------------------ Export to Qiskit for Visualization ---------------------

public export
unitarytoQVisNoBarrier : Unitary n -> String
unitarytoQVisNoBarrier IdGate = ""
unitarytoQVisNoBarrier (H i g) = unitarytoQVis g ++  "\tcircuit.h(" ++ show i ++ ")\n"
unitarytoQVisNoBarrier (P p i g) = unitarytoQVis g ++ "\tcircuit.p(" ++ printPhase p 0.001 "np.pi" ++ ", "++ show i ++ ")\n" 
unitarytoQVisNoBarrier (CNOT c t g) = unitarytoQVis g ++ "\tcircuit.cx(" ++ show c ++ ", " ++ show t ++ ")\n" 


private
toQVisNoBarrier : {n : Nat} -> Unitary n -> String
toQVisNoBarrier g =
  let s = unitarytoQVisNoBarrier g in
  ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n" ++
  "def OutputCircuit():  \n" ++
  "\tcircuit = QuantumCircuit(" ++ show n ++ ")\n" ++ s ++
  "\treturn circuit \n\nqc = OutputCircuit()")

|||Export a circuit to Qiskit code
public export
exportForQVisNoBarrier : {n : Nat} -> String -> Unitary n -> IO ()
exportForQVisNoBarrier str g =
  let s = toQVisNoBarrier g in
      do
        a <- writeFile str s
        case a of
             Left e1 => putStrLn "Error when writing file"
             Right io1 => pure ()