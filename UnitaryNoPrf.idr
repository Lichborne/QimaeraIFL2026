module UnitaryNoPrf

import Data.Vect
import Data.Nat
import System.File
import Injection
import Lemmas
import Data.DPair

infixr 9 .
infixr 10 #

%default total

------------------------Local Lemmas and Utilities -------------

|||THIS IS STRICTLY FOR UnitaryNoPrf and applyUnitary'
public export
indexNoPrf : (k : Nat) -> Vect n Nat -> Nat
indexNoPrf Z     (x::_)  = x
indexNoPrf _ [] = Z
indexNoPrf (S k) (_::xs) = indexNoPrf k xs

------------------------QUANTUM CIRCUITS-----------------------

public export
data UnitaryNoPrf : Nat -> Type where
  IdGate : UnitaryNoPrf n
  H      : (j : Nat) -> (1 _ : UnitaryNoPrf n) -> UnitaryNoPrf n
  P      : (p : Double) -> (j : Nat) -> (1 _ : UnitaryNoPrf n) -> UnitaryNoPrf n
  CNOT   : (c : Nat) -> (t : Nat) -> (1 _ : UnitaryNoPrf n) -> UnitaryNoPrf n

-------------------------------APPLY---------------------------
|||Apply a smaller circuit of size i to a bigger one of size n
|||The vector of wires on which we apply the circuit must follow some constraints:
|||All the indices must be smaller than n, and they must be all different
public export
apply : {i : Nat} -> {n : Nat} -> 
        (1 _ : UnitaryNoPrf i) -> (1 _ : UnitaryNoPrf n) -> 
        (v : Vect i Nat) -> UnitaryNoPrf n
apply IdGate g2 _ = g2
apply (H j g1) g2 v = H (indexNoPrf j v) (apply g1 g2 v)
apply (P p j g1) g2 v = P p (indexNoPrf j v) (apply g1 g2 v)
apply {i} {n} (CNOT c t g1) g2 v = CNOT (indexNoPrf c v) (indexNoPrf t v) (apply g1 g2 v)

---------------------------COMPOSE-----------------------------
|||Compose 2 circuits of the same size
public export
compose : (1 _ : UnitaryNoPrf n) -> (1 _ : UnitaryNoPrf n) -> UnitaryNoPrf n
compose IdGate g1 = g1
compose (H j g1) g2 = H j (compose g1 g2)
compose (P p j g1) g2 = P p j (compose g1 g2)
compose (CNOT c t g1) g2 = CNOT c t (compose g1 g2)

export
composeN : {n:Nat} -> (1 _ : UnitaryNoPrf n) -> (1 _ : UnitaryNoPrf n) -> UnitaryNoPrf n
composeN IdGate g1 = g1
composeN (H j g1) g2 = H j (compose g1 g2)
composeN (P p j g1) g2 = P p j (compose g1 g2)
composeN (CNOT c t g1) g2 = CNOT c t (compose g1 g2)

public export
(.) : (1 _ : UnitaryNoPrf n) -> (1 _ : UnitaryNoPrf n) -> UnitaryNoPrf n
(.) = compose 

---------------------------ADJOINT-----------------------------
|||Find the adjoint of a circuit
public export
adjoint : UnitaryNoPrf n -> UnitaryNoPrf n
adjoint IdGate = IdGate
adjoint (H j g) = (adjoint g) . (H j IdGate)
adjoint (P p j g) = (adjoint g) . (P (-p) j IdGate)
adjoint (CNOT c t g) = (adjoint g) . (CNOT c t IdGate)


---------------------TENSOR PRODUCT----------------------------
|||Make the tensor product of two circuits
public export
tensor : {n : Nat} -> {p : Nat} -> (1 _ : UnitaryNoPrf n) -> ( 1 _ : UnitaryNoPrf p) -> UnitaryNoPrf (n + p)
tensor g1 g2 = apply g2 (apply g1 (IdGate {n = n+p}) (rangeVect 0 n)) (rangeVect n p)

public export
(#) : {n : Nat} -> {p : Nat} -> (1 _ : UnitaryNoPrf n) -> (1 _ : UnitaryNoPrf p) -> UnitaryNoPrf (n + p)
(#) = tensor

----------------------CLASSICAL GATES--------------------------
public export
HGate : UnitaryNoPrf 1
HGate = H 0 IdGate

public export
PGate : Double -> UnitaryNoPrf 1
PGate r = P r 0 IdGate

public export
CNOTGate : UnitaryNoPrf 2
CNOTGate = CNOT 0 1 IdGate

public export
T : (j : Nat) -> UnitaryNoPrf n -> UnitaryNoPrf n
T j g = P (pi/4) j g

public export
TGate : UnitaryNoPrf 1
TGate = T 0 IdGate

public export
TAdj : (j : Nat) -> UnitaryNoPrf n -> UnitaryNoPrf n
TAdj j g = P (-pi/4) j g

public export
TAdjGate : UnitaryNoPrf 1
TAdjGate = TAdj 0 IdGate

public export
S : (j : Nat) -> UnitaryNoPrf n -> UnitaryNoPrf n
S j g = P (pi/2) j g

public export
SGate : UnitaryNoPrf 1
SGate = S 0 IdGate

public export
SAdj : (j : Nat) ->  UnitaryNoPrf n -> UnitaryNoPrf n
SAdj j g = P (-pi/2) j g

public export
SAdjGate : UnitaryNoPrf 1
SAdjGate = SAdj 0 IdGate

public export
Z : (j : Nat) -> UnitaryNoPrf n -> UnitaryNoPrf n
Z j g = P pi j g

public export
ZGate : UnitaryNoPrf 1
ZGate = Z 0 IdGate

public export
X : (j : Nat) -> UnitaryNoPrf n -> UnitaryNoPrf n
X j g = H j (Z j (H j g))

public export
XGate : UnitaryNoPrf 1
XGate = X 0 IdGate

public export
RxGate : Double -> UnitaryNoPrf 1
RxGate p = HGate . PGate p . HGate

public export
RyGate : Double -> UnitaryNoPrf 1
RyGate p = SAdjGate . HGate . PGate (-p) . HGate . SGate

public export
RzGate : Double -> UnitaryNoPrf 1
RzGate p = PGate p 

public export
CX : (n: Nat) -> ( m: Nat) -> UnitaryNoPrf m
CX a b = (CNOT 0 a (IdGate))

public export
RZCX : (gamma: Double) -> {n:Nat} -> {m:Nat} -> UnitaryNoPrf m
RZCX g {n} {m} = (P g n (CX n m))


---------------------CONTROLLED VERSIONS-----------------------
|||Toffoli gate
public export
toffoli : UnitaryNoPrf 3
toffoli = 
  let g1 = CNOT 1 2 (H 2 IdGate)
      g2 = CNOT 0 2 (TAdj 2 g1)
      g3 = CNOT 1 2 (T 2 g2)
      g4 = CNOT 0 2 (TAdj 2 g3)
      g5 = CNOT 0 1 (T 1 (H 2 (T 2 g4)))
  in CNOT 0 1 (T 0 (TAdj 1 g5))

|||Controlled Hadamard gate
public export
controlledH : UnitaryNoPrf 2
controlledH =
  let h1 = (IdGate {n=1}) # (SAdjGate . HGate . TGate . HGate . SGate)
      h2 = (IdGate {n=1}) # (SAdjGate . HGate . TAdjGate . HGate . SGate)
  in h1 . CNOTGate . h2

|||Controlled phase gate
public export
controlledP : Double -> UnitaryNoPrf 2
controlledP p = 
  let p1 = CNOT 0 1 (P (p/2) 1 IdGate)
  in CNOT 0 1 (P (-p/2) 1 p1)

|||Make the controlled version of a gate
public export
controlled : {n : Nat} -> (1 _ :UnitaryNoPrf n) -> UnitaryNoPrf (S n)
controlled IdGate = IdGate
controlled (H j g) = apply {i = 2} {n = S n} controlledH (controlled g) [0, S j]
controlled (P p j g) = apply {i = 2} {n = S n} (controlledP p) (controlled g) [0, S j]
controlled (CNOT c t g) = apply {i = 3} {n = S n} toffoli (controlled g) [0, S c, S t]

public export
multipleControlled:  {n : Nat} -> (k : Nat) -> (1 _ :UnitaryNoPrf n) -> UnitaryNoPrf (k + n)
multipleControlled Z un = un
multipleControlled (S m) un = controlled $ multipleControlled m un

------------SOME USEFUL FUNCTIONS FOR CREATING GATES-----------

|||Make n tensor products of the same UnitaryNoPrf of size 1
public export
tensorn : (n : Nat) -> UnitaryNoPrf 1 -> UnitaryNoPrf n
tensorn 0 _ = IdGate
tensorn (S k) g = g # (tensorn k g)

|||Controls on the n-1 first qubits, target on the last
public export
generalizedToffoli : (n : Nat) -> UnitaryNoPrf n
generalizedToffoli 0 = IdGate
generalizedToffoli 1 = IdGate
generalizedToffoli 2 = CNOT 0 1 IdGate
generalizedToffoli (S k) = controlled (generalizedToffoli k)

||| Tensor product of a Vector of UnitaryNoPrf operators
export
tensorMap : {n : Nat} -> {m : Nat} -> (gates : Vect n (UnitaryNoPrf m)) -> UnitaryNoPrf (n*m)
tensorMap [] = IdGate
tensorMap (gate :: gates) = gate # (tensorMap gates)

||| Tensor product of a Vector of single-qubit UnitaryNoPrf operators
export
tensorMapSimple : {n : Nat} -> (gates : Vect n (UnitaryNoPrf 1)) -> UnitaryNoPrf n
tensorMapSimple g = rewrite sym $ multOneRightNeutral n in tensorMap g

---------------------------------------------------------------
-- count the total number of atomic gates in a UnitaryNoPrf circuit
export
gateCount : UnitaryNoPrf n -> Nat
gateCount IdGate = 0
gateCount (H j x) = S (gateCount x)
gateCount (P p j x) = S (gateCount x)
gateCount (CNOT c t x) = S (gateCount x)

--count the number of H gates in a UnitaryNoPrf circuit
export
Hcount : UnitaryNoPrf n -> Nat
Hcount IdGate = 0
Hcount (H j x) = S (Hcount x)
Hcount (P p j x) = Hcount x
Hcount (CNOT c t x) = Hcount x

--count the number of P gates in a UnitaryNoPrf circuit
export
Pcount : UnitaryNoPrf n -> Nat
Pcount IdGate = 0
Pcount (H j x) = Pcount x
Pcount (P p j x) = S (Pcount x)
Pcount (CNOT c t x) = Pcount x


--count the number of CNOT gates in a UnitaryNoPrf circuit
export
CNOTcount : UnitaryNoPrf n -> Nat
CNOTcount IdGate = 0
CNOTcount (H j x) = CNOTcount x
CNOTcount (P p j x) = CNOTcount x
CNOTcount (CNOT c t x) = S (CNOTcount x)

----------------------------DEPTH------------------------------
|||Compute the depth of  circuit

addDepthNoPrf : Nat -> (j : Nat) -> Vect n Nat -> Vect n Nat
addDepthNoPrf _ 0 [] = []
addDepthNoPrf _ (S _) [] = []
addDepthNoPrf j 0 (x :: xs) = j :: xs
addDepthNoPrf j (S k) (x :: xs) = x :: addDepthNoPrf j k xs 

findValueNoPrf : (j : Nat) -> Vect n Nat -> Nat
findValueNoPrf 0 [] = Z
findValueNoPrf (S _) [] = Z
findValueNoPrf 0 (x::xs) = x
findValueNoPrf (S k) (x::xs) = findValueNoPrf k xs 

depth' : {n : Nat} -> UnitaryNoPrf n -> Vect n Nat
depth' IdGate = replicate n 0
depth' (H j x) =
  let v = depth' x 
      k = findValueNoPrf j v
  in addDepthNoPrf (S k) j v
depth' (P p j x) = 
  let v = depth' x
      k = findValueNoPrf j v
  in addDepthNoPrf (S k) j v
depth' (CNOT c t x) = 
  let v = depth' x 
      k = findValueNoPrf c v
      m = findValueNoPrf t v
  in if k < m then
              let w = addDepthNoPrf (S m) c v
              in addDepthNoPrf (S m) t w
     else
              let w = addDepthNoPrf (S k) c v
              in addDepthNoPrf (S k) t w

export
depth : {n : Nat} -> UnitaryNoPrf n -> Nat
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
Show (UnitaryNoPrf n) where
  show IdGate = ""
  show (H j x) = "(H " ++ show j ++ ") " ++ show x 
  show (P p j x) = "(P " ++ printPhase p 0.001 "π" ++ " " ++ show j ++ ") " ++ show x
  show (CNOT c t x) = "(CNOT " ++ show c ++ " " ++ show t ++ ") " ++ show x



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

export
drawGate : {n : Nat} -> UnitaryNoPrf n -> Vect n String
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


export
drawVect : Vect n String -> String
drawVect [] = ""
drawVect (x :: xs) = x ++ "\n" ++ drawVect xs

|||Draw a circuit in the terminal
public export
draw : {n : Nat} ->  UnitaryNoPrf n -> IO ()
draw g =
  let vs1 = drawGate {n} g in
  let s = drawVect vs1 in
  putStrLn s



--------------------------EXPORT TO QISKIT---------------------

public export
UnitaryNoPrftoQiskit : UnitaryNoPrf n -> String
UnitaryNoPrftoQiskit IdGate = ""
UnitaryNoPrftoQiskit (H i g) = UnitaryNoPrftoQiskit g ++  "qc.h(qr[" ++ show i ++ "])\nqc.barrier(qr)\n"
UnitaryNoPrftoQiskit (P p i g) = UnitaryNoPrftoQiskit g ++ "qc.p(" ++ printPhase p 0.001 "np.pi" ++ ", qr[" ++ show i ++ "])\nqc.barrier(qr)\n" 
UnitaryNoPrftoQiskit (CNOT c t g) = UnitaryNoPrftoQiskit g ++ "qc.cx(qr[" ++ show c ++ "], qr[" ++ show t ++ "])\nqc.barrier(qr)\n" 


public export
toQiskit : {n : Nat} -> UnitaryNoPrf n -> String
toQiskit g =
  let s = UnitaryNoPrftoQiskit g in
  ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n" ++
  "from qiskit import QuantumRegister\n" ++
  "qr = QuantumRegister(" ++ show n ++ ")\n" ++
  "qc = QuantumCircuit(qr)\n\n" ++ s ++
  "\nprint(qc)")


|||Export a circuit to Qiskit code
public export
exportToQiskit : {n : Nat} -> String -> UnitaryNoPrf n -> IO ()
exportToQiskit str g =
  let s = toQiskit g in
      do
        a <- writeFile str s
        case a of
             Left e1 => putStrLn "Error when writing file"
             Right io1 => pure ()

private
toQiskitWithSize : {n : Nat} -> (size: Nat) -> UnitaryNoPrf n -> String
toQiskitWithSize sz g =
  let s = UnitaryNoPrftoQiskit g in
  ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n" ++
  "from qiskit import QuantumRegister\n" ++
  "qr = QuantumRegister(" ++ show sz ++ ")\n" ++
  "qc = QuantumCircuit(qr)\n\n" ++ s ++
  "\nqc.draw('mpl')")

|||Export a circuit to Qiskit code
public export
exportToQiskitWithSize : {n : Nat} -> String -> (size: Nat) -> UnitaryNoPrf n -> IO ()
exportToQiskitWithSize str sz g =
  let s = toQiskitWithSize sz g in
      do
        a <- writeFile str s
        case a of
             Left e1 => putStrLn "Error when writing file"
             Right io1 => pure ()

------------------ Export to Qiskit for Visualization ---------------------

public export
unitarytoQVis : UnitaryNoPrf n -> String
unitarytoQVis IdGate = ""
unitarytoQVis (H i g) = unitarytoQVis g ++  "\tcircuit.h(" ++ show i ++ ")\n"
unitarytoQVis (P p i g) = unitarytoQVis g ++ "\tcircuit.p(" ++ printPhase p 0.001 "np.pi" ++ ", "++ show i ++ ")\n" 
unitarytoQVis (CNOT c t g) = unitarytoQVis g ++ "\tcircuit.cx(" ++ show c ++ ", " ++ show t ++ ")\n" 

private
toQVis : {n : Nat} -> UnitaryNoPrf n -> String
toQVis g =
  let s = unitarytoQVis g in
  ("import numpy as np\n" ++
  "from qiskit import QuantumCircuit\n" ++
  "def OutputCircuit():  \n" ++
  "\tcircuit = QuantumCircuit(" ++ show n ++ ")\n" ++ s ++
  "\treturn circuit \n\nqc = OutputCircuit()")

|||Export a circuit to Qiskit code
public export
exportForQVis : {n : Nat} -> String -> UnitaryNoPrf n -> IO ()
exportForQVis str g =
  let s = toQVis g in
      do
        a <- writeFile str s
        case a of
             Left e1 => putStrLn "Error when writing file"
             Right io1 => pure ()             