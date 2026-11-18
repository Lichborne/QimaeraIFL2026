module ModularExponentiation

import Data.Nat
import Data.Vect
import Decidable.Equality
import Injection
import QuantumOp
import LinearTypes
import UStateT
import QStateT
import UnitaryLinear
import QFT
import Lemmas
import UnitarySim
import QuantumOp
import OptimiseUnitary
import NatRules
import UnitaryNoPrf
import UnitaryNoPrfSim

------------------------Quantum Modular Exponentiation------------------------

||| This file contains the implementation of QME following Beauregard,
||| "Circuit for Shor's algorithm using 2n+3 qubits" (2003). As in the paper,
||| a and N are classical numbers built into the circuit: everything that
||| depends only on them (a^p mod N, a^(-1) mod N, 2^k a mod N) is computed
||| classically while the circuit is built, and the quantum registers are the
||| control c, an ancilla, x (i qubits) and b (i + 1 qubits).
||| The in-place QFT adder of two quantum registers is kept as a separate example.



--------------- CLASSICAL preprocessing ---------------

||| a^n mod N and its inverse mod N (which exists when gcd(a, N) = 1) are
||| computed classically and built into the circuit, as in Beauregard.

------------------------------------------------------------------------------

toIntegerNat : Nat -> Integer
toIntegerNat Z = 0
toIntegerNat (S k) = 1 + toIntegerNat k

extgcd : Integer -> Integer -> Pair Integer Integer
extgcd 0 b = (0, 1)
extgcd a b = let 
                (x', y') = extgcd (b `mod` a) a
                x = y' - (b `div` a) * x'
                y = x'
              in (x, y)

||| a^(-1) mod m, for gcd(a, m) = 1
export
modInverse : Nat -> Nat -> Nat
modInverse a m = let x = fst $ extgcd (toIntegerNat a) (toIntegerNat m)
                     r = x `mod` toIntegerNat m
                 in fromInteger (if r < 0 then r + toIntegerNat m else r)

||| a^e mod m, by repeated squaring
export
powMod : Nat -> Nat -> Nat -> Nat
powMod a e m = go (a `mod` m) e (1 `mod` m) where
  go : Nat -> Nat -> Nat -> Nat
  go b Z acc = acc
  go b e acc = go ((b * b) `mod` m) (e `div` 2) (if e `mod` 2 == 1 then (acc * b) `mod` m else acc)


---------------IN-PLACE QFT ADDER (two quantum registers)---------------
||| Expects inputs in big-endian order; b has one more qubit than a, its first
||| qubit taking the overflow: |a>|b> -> |a>|(b + a) mod 2^(i+1)>.
-----------------------------------------------


||| a_0, a_1, ... control R_m, R_(m+1), ... on the qubit b
addWithQFTHelp : UnitaryOp t => {k : Nat} -> {n: Nat} -> (1_ : LVect k Qubit) 
                                    -> (1_ : Qubit) -> (m : Nat) -> UStateT (t n) (t n) ((LVect (S k) Qubit))
addWithQFTHelp LinearTypes.Nil b _ = pure $ [b]
addWithQFTHelp (a::as) b m = do
    [a,b] <- applyUnitary [a,b] (cRmOld m) 
    b::as <- addWithQFTHelp as b (S m)
    pure $ (b::a::as)

||| Adds a to b (both i qubits, b in Fourier space): b_k gets R_1 from a_k, R_2 from a_(k+1), ...
addAligned : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect i Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect i Qubit))
addAligned [] [] = pure ([] # [])
addAligned (a :: as) (b :: bs) = do
   (b :: a :: as) <- addWithQFTHelp (a :: as) b 1
   as # bs <- addAligned as bs
   pure ((a :: as) # (b :: bs))

||| Adds a (i qubits) to b (i + 1 qubits, in Fourier space): the overflow qubit of b
||| gets R_2, R_3, ... from a; the remaining i qubits of b are aligned with a.
addWithQFT: UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) ((LVect  (i + S i)  Qubit))
addWithQFT as (b :: bs) = do
   (b :: as) <- addWithQFTHelp as b 2
   as # bs <- addAligned as bs
   pure $ (++) as (b::bs)

||| Split version of the in-place adder. 
export
inPlaceQFTAdderSplit : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect (S i) Qubit))
inPlaceQFTAdderSplit [] b = pure $ [] # b
inPlaceQFTAdderSplit a [] impossible
inPlaceQFTAdderSplit {i = S k} (a :: as) (b::bs) = do --pattern matching requires that the lvects be of this form for some reason - idris can be strange
    qftbs <- (qft (b::bs))
    all <- addWithQFT (a :: as) qftbs
    addAs # addBs <- splitQubitsInto (S k) (S (S k)) all 
    unqftbs <- (qftAdj (addBs))
    pure $ addAs # unqftbs     

||| The above could be used directly, but this is done instead as an exercises
export
inPlaceQFTAdder : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect (i + S i) Qubit) -> UStateT (t n) (t n) ((LVect (i + S i) Qubit))
inPlaceQFTAdder {i = Z} [b] = pure $ [b] -- since the form of the lvect is i + S i, it is at least one
inPlaceQFTAdder {i = S k} (a::asbbs) = do --pattern matching requires that the lvects be of this form for some reason - idris can be strange
    as # bs <- splitQubitsInto (S k) (S (S k)) (a::asbbs)
    qftbs <- (qft (bs))
    all <- addWithQFT (as) qftbs
    addAs # addBs <- splitQubitsInto (S k) (S (S k)) all 
    unqftbs <- (qftAdj (addBs))
    pure $ (++) addAs unqftbs  

export
inPlaceQFTAdderInv : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect (i + S i) Qubit) -> UStateT (t n) (t n) ((LVect (i + S i) Qubit))
inPlaceQFTAdderInv lv = adjointUST $ inPlaceQFTAdder lv

---------------CONSTANT ADDER IN FOURIER SPACE (Beauregard's phiADD(a))---------------
||| b is a register of k qubits in Fourier space (after qft; big-endian). There its
||| first qubit carries the phase 2 pi b / 2^k, the next 2 pi b / 2^(k-1), and so on,
||| so adding the classical number a is one phase gate per qubit: b -> (b + a) mod 2^k.
export
phiAdd : UnitaryOp t => {n : Nat} -> {k : Nat} -> (a : Nat) -> (1 _ : LVect k Qubit) -> UStateT (t n) (t n) (LVect k Qubit)
phiAdd a [] = pure []
phiAdd {k = S j} a (q :: qs) = do
    [q] <- phase (a `mod` power 2 (S j)) (S j) q
    qs <- phiAdd a qs
    pure (q :: qs)
  where
    ||| P(2 pi m / 2^k), or nothing if m = 0
    phase : (m : Nat) -> (k : Nat) -> (1 _ : Qubit) -> UStateT (t n) (t n) (LVect 1 Qubit)
    phase Z k q = pure [q]
    phase m k q = applyP (2 * pi * cast m / cast (power 2 k)) q

---------------MODULAR ADDER (Beauregard's doubly controlled phiADD(a)MOD(N))---------------
||| b has i + 1 qubits (the first takes the overflow) and is in Fourier space before and
||| after. If both controls are set, b -> (b + a) mod N; otherwise b is unchanged.
||| Requires a < N, b < N and N < 2^i; the ancilla starts and ends in |0>.
export
phiAddModN : UnitaryOp t => {n : Nat} -> {i : Nat} -> (a : Nat) -> (bigN : Nat)
          -> (1 c1 : Qubit) -> (1 c2 : Qubit) -> (1 ancilla : Qubit) -> (1 b : LVect (S i) Qubit)
          -> UStateT (t n) (t n) (LVect (3 + S i) Qubit)
phiAddModN a bigN c1 c2 ancilla b = do
    (c1 :: c2 :: b) <- multipleControlUST [c1, c2] b (phiAdd a)    -- b + a
    b <- adjointUST (phiAdd bigN b)                                 -- b + a - N
    (s :: bs) <- qftAdj b
    [s, ancilla] <- applyCNOT s ancilla                             -- ancilla = 1 iff b + a < N
    b <- qft (s :: bs)
    (ancilla :: b) <- controlUST ancilla b (phiAdd bigN)            -- (b + a) mod N
    (c1 :: c2 :: b) <- multipleControlUST [c1, c2] b (\qs => adjointUST (phiAdd a qs))
    (s :: bs) <- qftAdj b                                           -- (b + a) mod N - a < 0 iff ancilla = 0
    [s] <- applyUnitary [s] XGate
    [s, ancilla] <- applyCNOT s ancilla                             -- so this resets the ancilla
    [s] <- applyUnitary [s] XGate
    b <- qft (s :: bs)
    (c1 :: c2 :: b) <- multipleControlUST [c1, c2] b (phiAdd a)    -- (b + a) mod N
    pure (c1 :: c2 :: ancilla :: b)

---------------CONTROLLED MODULAR MULTIPLIER (Beauregard's CMULT(a)MOD(N))---------------

||| Adds (2^k a mod N) x_k, controlled by c, for each qubit x_k of x (big-endian, so the
||| first of j qubits has weight 2^(j-1)). b is in Fourier space; requires b < N.
phiMultAdd : UnitaryOp t => {n : Nat} -> {j : Nat} -> {i : Nat} -> (a : Nat) -> (bigN : Nat)
          -> (1 c : Qubit) -> (1 ancilla : Qubit) -> (1 x : LVect j Qubit) -> (1 b : LVect (S i) Qubit)
          -> UStateT (t n) (t n) (LPair (LVect 2 Qubit) (LPair (LVect j Qubit) (LVect (S i) Qubit)))
phiMultAdd a bigN c ancilla [] b = pure ([c, ancilla] # ([] # b))
phiMultAdd {j = S k} a bigN c ancilla (x :: xs) b = do
    (c :: x :: ancilla :: b) <- phiAddModN ((power 2 k * a) `mod` bigN) bigN c x ancilla b
    [c, ancilla] # (xs # b) <- phiMultAdd a bigN c ancilla xs b
    pure ([c, ancilla] # ((x :: xs) # b))

||| On c, ancilla, x (i qubits), b (i + 1 qubits): b -> (b + a x) mod N if c is set.
||| Requires b < N; the ancilla starts and ends in |0>.
export
cMultModN : UnitaryOp t => {n : Nat} -> {i : Nat} -> (a : Nat) -> (bigN : Nat)
         -> (1 _ : LVect (2 + i + S i) Qubit) -> UStateT (t n) (t n) (LVect (2 + i + S i) Qubit)
cMultModN a bigN (c :: ancilla :: xb) = do
    x # b <- splitQubitsInto i (S i) xb
    b <- qft b
    [c, ancilla] # (x # b) <- phiMultAdd a bigN c ancilla x b
    b <- qftAdj b
    pure (c :: ancilla :: (x ++ b))

---------------CONTROLLED SWAP---------------

||| Swaps two registers with three CNOTs per pair of qubits. Unlike reordering the
||| output vector (swapRegistersByLength), this is a circuit, so it can be controlled.
swapRegisterGates : UnitaryOp t => {n : Nat} -> {i : Nat} -> (1 _ : LVect i Qubit) -> (1 _ : LVect i Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect i Qubit))
swapRegisterGates [] [] = pure ([] # [])
swapRegisterGates (p :: ps) (q :: qs) = do
    [p, q] <- applyCNOT p q
    [q, p] <- applyCNOT q p
    [p, q] <- applyCNOT p q
    ps # qs <- swapRegisterGates ps qs
    pure ((p :: ps) # (q :: qs))

swapHalves : UnitaryOp t => {n : Nat} -> {i : Nat} -> (1 _ : LVect (i + i) Qubit) -> UStateT (t n) (t n) (LVect (i + i) Qubit)
swapHalves qs = do
    ps # rs <- splitQubitsInto i i qs
    ps # rs <- swapRegisterGates ps rs
    pure (ps ++ rs)

---------------CONTROLLED MODULAR MULTIPLICATION (Beauregard's controlled U_a)---------------

||| |c>|x>|0> -> |c>|a x mod N>|0> if c is set, otherwise unchanged. Requires x < N,
||| aInv = a^(-1) mod N and N < 2^i; the ancilla starts and ends in |0>.
||| Returns c, the ancilla and b (whose i + 1 qubits are back to |0>), and then x.
export
inPlaceModularExponentiation : UnitaryOp t => {n : Nat} -> {i : Nat} -> (a : Nat) -> (aInv : Nat) -> (bigN : Nat)
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect i Qubit) -- this is x represented in i qubits
                                -> (1 nils : LVect (S i) Qubit) -- this should be |0>(S i): b, with the overflow qubit first
                                -> UStateT (t n) (t n) (LPair (LVect (3 + i) Qubit) (LVect i Qubit))
inPlaceModularExponentiation a aInv bigN [c] [ancilla] x nils = do
    (c :: ancilla :: xb) <- cMultModN a bigN (c :: ancilla :: (x ++ nils))      -- b = a x mod N
    x # (ovf :: b) <- splitQubitsInto i (S i) xb
    (c :: xb) <- controlUST c (x ++ b) (swapHalves {i = i})                      -- x <-> b
    x # b <- splitQubitsInto i i xb
    (c :: ancilla :: xb) <- adjointUST (cMultModN aInv bigN (c :: ancilla :: (x ++ (ovf :: b))))  -- b = x - aInv (a x) mod N = 0
    x # b <- splitQubitsInto i (S i) xb
    pure ((c :: ancilla :: b) # x)


--------------- Basic encoding on natural numbers  into register of size i --------------   

data Bit : Type where 
    B0 : Bit
    B1 : Bit

||| The i lowest bits of num, most significant first (big-endian, as everywhere in this file)
natToBinIVect : (i: Nat) -> (num:Nat) -> Vect i Bit
natToBinIVect Z _ = []
natToBinIVect (S k) num = (if (num `div` power 2 k) `mod` 2 == 1 then B1 else B0) :: natToBinIVect k num

||| Takes a vector of Bins and a vector of qubits expected to be in |0>^n, and returns the unitary operation of encoding the number in the qubits
||| helper for making the below more efficient
binVectToUnitaryI : UnitaryOp t => {i:Nat} -> {n:Nat} -> (bitv: Vect i Bit) -> (1_ : LVect i Qubit) -> UStateT (t n) (t n) ( LVect i Qubit)
binVectToUnitaryI {i = Z} [] [] = pure []
binVectToUnitaryI (x::xs) [] impossible -- because i = i
binVectToUnitaryI [] (q::qs) impossible 
binVectToUnitaryI {i = S k} (x::xs) (q::qs) = case x of 
    B0 => do
         qss <- (binVectToUnitaryI xs qs)
         pure (q :: qss)
    B1 => do
        [q1] <- applyUnitary {n} {i = 1} [q] XGate
        qss <- (binVectToUnitaryI xs qs)
        pure (q1 :: qss)

||| Takes a Nat and a vector of qubits expected to be in |0>^n, and returns the unitary operation of encoding the number in the qubits
||| It keeps the i lowest bits of the number if the qubits are not enough to contain it, otherwise it pads with zeros on the left
natToUnitaryI : UnitaryOp t => {i:Nat} -> {n:Nat} -> (num:Nat) -> (1_ : LVect i Qubit) -> UStateT (t n) (t n) (LVect i Qubit)
natToUnitaryI _ [] = pure []
natToUnitaryI Z (q::qs) = pure (q::qs)
natToUnitaryI {i = (S k)} (S n) (q::qs) = binVectToUnitaryI (natToBinIVect (S k) (S n)) (q::qs)

export
||| modular exponentiation using QuantumOp and UnitaryOp: prepares x, then applies
||| x -> a^n x mod N, controlled by c (classical preprocessing: a^n mod N and its inverse)
modularExponentiationOp: QuantumOp t => UnitaryOp t => 
                                                     (1_ : LVect 1 Qubit) -- the control, comes from a different computation, 
                                                    -> (i:Nat) -> (n:Nat) -> (x : Nat) -> (a:Nat) -> (bigN: Nat)
                                                    -> QStateT (t 1) (t (2 + i + (S i))) ((LVect (3 + i + i) Qubit))
modularExponentiationOp {t = t} c i n x a bigN = let 
                                          an = powMod a n bigN
                                          anmodinv = modInverse an bigN
                                        in
                                            do 
                                                ancilla <- newQubit {t = t} 
                                                xs0 <- newQubits {t = t} i
                                                xs <- applyUST {t = t} (natToUnitaryI x xs0)
                                                bsZeros <- newQubits {t = t} (S i)
                                                output <- applyUST (combineAbs $ inPlaceModularExponentiation an anmodinv bigN c [ancilla] xs bsZeros)
                                                pure (output)
                                                      
-------------------- Unitary part of QME test --------------------------

||| The controlled multiplication x -> a x mod N as a Unitary on 2 + i + (i + 1) qubits:
||| wires c, ancilla, then x, then b (overflow qubit first).
export
modularN : (i : Nat) -> (a : Nat) -> (bigN : Nat) -> Unitary (2 + i + S i)
modularN i a bigN = buildUnitary {t = Unitary} (\qs => do
        [c, ancilla] # rest <- splitQubitsInto 2 (i + S i) qs
        x # nils <- splitQubitsInto i (S i) rest
        (c :: ancilla :: b) # x <- inPlaceModularExponentiation a (modInverse a bigN) bigN [c] [ancilla] x nils
        pure (c :: ancilla :: (x ++ b)))

||| testing the unitary part of modular exponentiation: 7 x mod 15
export
modularTestSmall : (Unitary 11)
modularTestSmall = modularN 4 7 15

||| Larger test (takes a while): 33 qubits, N = 32399 = 179*181
export
modularTest : (Unitary 33)
modularTest = modularN 15 7 32399

||| Gate counts for the modular exponentiation circuit (modularTest) Takes a few minutes on a normal laptop
modularTestGateCount: List Nat
modularTestGateCount = let gate = modularTest in
    let gates = gateCount gate 
        hs = Hcount gate
        ps = Pcount gate
        cnots = CNOTcount gate
        in [gates, hs, ps, cnots]

{-
 modularTestGateCount
[132694,
6862,
73776,
52056]
-}

||| Optimisation and gatecount thereof of modularTest. This takes a long time.
modularTestOpt : Nat
modularTestOpt = gateCount (optimise modularTest)

