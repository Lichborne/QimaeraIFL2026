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

||| This file contains the implementation of QME
||| The first few functions are defined using two approaches, 
||| with the alternate version found at the bottom.
||| One, where the computationally most relevant set of qubits
||| for a given function is separated out throughout the implementation,
||| and one where everyting is done as usual. This is to be able to
||| compare if the former works as intended. The final implementation is given using this.



--------------- CLASSICAL modular inverse when we know gcd = 1 ---------------

||| An implementation of this is necessary for the below quantum implementation
||| to be feasible (for calculating a^-1 mod N as well as a^n mod N, when we
||| know gcd = 1) This is only utilized at the very end, but reference is made 
||| to it for design choices (see also Beauregard 2002)

------------------------------------------------------------------------------

toIntegerNat : Nat -> Integer
toIntegerNat Z = 0
toIntegerNat (S k) = 1 + toIntegerNat k

abs : Integer -> Integer 
abs x = if x >= 0 then x else x + (2 * (-x))

extgcd : Integer -> Integer -> Pair Integer Integer
extgcd 0 b = (0, 1)
extgcd a b = let 
                (x', y') = extgcd (b `mod` a) a
                x = y' - (b `div` a) * x'
                y = x'
              in (x, y)
    
modInverse : Nat -> Nat -> Nat
modInverse a m = fromInteger $ abs $ fst $ extgcd (toIntegerNat a) (toIntegerNat m)

---------------IN-PLACE QFT ADDER---------------
||| Expects inputs in big-endian order 
-----------------------------------------------


addWithQFTHelp : UnitaryOp t => {k : Nat} -> {n: Nat} -> (1_ : LVect k Qubit) 
                                    -> (1_ : Qubit) -> (m : Nat) -> UStateT (t n) (t n) ((LVect (S k) Qubit))
addWithQFTHelp LinearTypes.Nil b _ = pure $ [b]
addWithQFTHelp (a::as) b m = do
    [a,b] <- applyUnitary [a,b] (cRmOld m) 
    b::as <- addWithQFTHelp as b (S m)
    pure $ (b::a::as)

addWithQFT: UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) ((LVect  (i + S i)  Qubit))
addWithQFT [] b = pure $ b
addWithQFT a [] impossible
addWithQFT {i = S k} (a :: as) (b::bs) = do
   (b::a::as) <-  addWithQFTHelp (a :: as) b 1
   asbs <-  addWithQFT as bs   
   as # bs <- splitQubitsInto k (S k) asbs 
   pure $ (++) (a :: as) (b::bs)    

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

inPlaceQFTAdderInvSplit : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1_ : LVect i Qubit) -> (1_ : LVect (S i) Qubit) -> UStateT (t n) (t n) (LPair (LVect i Qubit) (LVect (S i) Qubit))
inPlaceQFTAdderInvSplit {n = n} {i = i} as bs = do
    asbs <- combine as bs
    addAsBs <- inPlaceQFTAdderInv asbs
    as # bs <- splitQubitsInto i (S i) addAsBs
    pure (as # bs)

---------------IN-PLACE MODULAR ADDER---------------       

export
inPlaceModularAdder : UnitaryOp t => {i: Nat} -> {n : Nat} 
                                -> (1 controls : LVect 2 Qubit) -- these are the controls c1 and c2
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla
                                -> (1 a : LVect i Qubit) -- this is a represented in i Qubits
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i Qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (3 + i + i)  Qubit) (LVect ((S i)) Qubit)) -- we collect the 2 controls, ancilla, a, and N in the same output LVect, and b in the other

inPlaceModularAdder [c1,c2] [ancilla] [] [] [q] = pure $ (c1::c2::[ancilla]) # [q]
inPlaceModularAdder {i = S k} {n} [c1,c2] [ancilla] (a::as) bigNs (b::bs) = do
    asbs <- combine (a::as) (b::bs)
    (c1::c2::asbs)<- multipleControlUST [c1,c2] asbs (inPlaceQFTAdder  {n = S k + S (S k)} {i = S k})
    as # bs <- splitQubitsInto (S k) (S (S k)) asbs
    bigNs # bs <-  inPlaceQFTAdderInvSplit bigNs (bs)
    (s::qibs) <- (qftAdj (bs)) -- the most signigifact bit in out case will be the first, which is where the overflow goes, so this is our control
    [s,ancilla] <- applyCNOT s ancilla
    invqftbs <- (qft (s::qibs))
    toAddInv <- combine bigNs invqftbs
    ancilla::bigNs_bs <- controlUST ancilla toAddInv (inPlaceQFTAdderInv {n = S k + S (S k)}  {i = S k})
    bigNs # bs <- splitQubitsInto (S k) (S (S k)) bigNs_bs
    asbs <- combine (as) (bs)
    (c1::c2::asbs) <- multipleControlUST [c1,c2] asbs (inPlaceQFTAdder {n = S k + S (S k)}  {i = S k})
    as # bs <- splitQubitsInto (S k) (S (S k)) asbs
    (s::qibs) <- (qftAdj (bs))
    [s] <- applyUnitary [s] XGate
    [s,ancilla] <- applyCNOT s ancilla
    [s] <- applyUnitary [s] XGate
    invqftbs <- (qft (s::qibs))
    asbs <- combine (as) (invqftbs)
    (c1::c2::asbs) <-  multipleControlUST [c1,c2] asbs (inPlaceQFTAdder {n = S k + S (S k)} {i = S k})
    as # bs <- splitQubitsInto (S k) (S (S k)) asbs
    aAndN <- combine as bigNs
    pure $ ((++) (c1::c2::[ancilla]) aAndN) # (bs)


---------------IN-PLACE MODULAR MULTIPLIER---------------

||| Helper function that does the reursion on x, using each bit as control. 
allControls: UnitaryOp t => {j:Nat} -> {i: Nat} -> {n : Nat} -> {auto prf: LTE j i} -- This is somewhat superfluous, because we can handle other inputs as well it just won't make sense anyway. if we remove this there is only 1 proof required
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect j Qubit) -- this is x represented in j qubits
                                -> (1 a : LVect i Qubit) -- this is a represented in i qubits
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (2 + j + i + i)  Qubit) (LVect ((S i)) Qubit))
allControls [c] [ancilla] [] [] [] q = pure $ [c, ancilla] # q
allControls [_] [_] [] (x :: xs) (ns::bigNs) [] impossible -- for some reason idris wants this case
allControls [c] [ancilla] (x:: xs) [] [] [q] impossible -- because of the way b is set up, the control wont be relevant for the additiona qubit anywa; this should not happen (condition LT j i is excluded for simplicity)
allControls [c] [ancilla] (x::xs) [] [] [q] impossible -- for some reason, needs separate case
allControls [c] [ancilla] [] (a::as) (ns::bigNs) (b::bs)= do ---for some reason, idris needs the (::) operators here to recognize coverage, again...
    aAndN <- combine (a::as) (ns::bigNs)
    pure $ ((++) (c::[ancilla]) aAndN) # (b::bs)
allControls {prf} {j = S r} {i = S h} [c] [ancilla] (x::xs) a bigNs b = do
    (c::x::ancilla::aAndN) # b2 <- inPlaceModularAdder [c,x] [ancilla] a bigNs b
    a # bigNs <- splitQubitsAt {prf = lteSiPlusSi} (S h) aAndN -- the compiler sometimes finds this sometimes doesnt
    (c::ancilla::all) # finalb <- allControls {j = r} {i = S h} {prf = fromLteSucc $ lteSuccRight prf} [c] [ancilla] (xs) a (rewrite sym $ plusMinusLeftCancel0 h (S h) in bigNs) b2 ---ONE PROOF is necessary, the other depends on the LT condition
    pure $ (c::ancilla::x::all) # finalb 

|||Intermediaty multiplication function, output is (b+ax) mod N if c=1 else b
cMultAModN: UnitaryOp t => {i: Nat} -> {n : Nat}
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect i Qubit) -- this is x represented in i qubits 
                                -> (1 a : LVect i Qubit) -- this is a represented in i qubits
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (2 + i + i + i)  Qubit) (LVect ((S i)) Qubit))
cMultAModN [c] [ancilla] [] [] [] [q] = pure $ [c,ancilla] # [q]
cMultAModN [_] [_] [] [] [] [] impossible
cMultAModN [c] [ancilla] (xs) (as) (bigNs) (bs) = do
    qftb <- (qft (bs))
    middleAll # middleB <- allControls [c] [ancilla] (xs) (as) (bigNs) qftb
    finalB <- (qftAdj middleB)
    pure $ middleAll # finalB

|||in place modular multiplication function
inPlaceModExp: UnitaryOp t => {i: Nat} -> {n : Nat}
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect i Qubit) -- this is x represented in j qubits
                                -> (1 a : LVect i Qubit) -- this is a represented in i qubits
                                -> (1 amodinv : LVect i Qubit) -- this is a^(-1) mod N represented in i qubits. The classical algorithm for calculating this
                                                        -- from a is included above given the theoretical assurances in Beuregard
                                                        -- Note that since the content of the registers has to be prepared elsewhere, this is perfectly fine to assume
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 nils : LVect (S i) Qubit) -- this should be |0>(S n) because we are actually trying to calculate (ax mod N)
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (2 + i + i + i + i)  Qubit) (LVect (S i) Qubit)) -- this time x contains the computationally relevant bit so that is given back separately
inPlaceModExp [c] [ancilla] [] [] [] [] [q] = pure $ [c,ancilla] # [q]
inPlaceModExp [_] [_] [] [] [] [] [] impossible
inPlaceModExp {i = S h} [c] [ancilla] (xs) (as) (asmodinv) (bigNs) (nils) = do
    (c::ancilla::cmulted) # (ovf::multnils) <- cMultAModN [c] [ancilla] xs as bigNs nils -- 
    xs # aAndN <- splitQubitsAt {prf = lteSiPlusPlusSi {i = h}} (S h) cmulted -- Proof 
    as # bigNs <- (splitQubitsAt {prf = plusMinusLeftCancelDeep {h = h}} (S h) aAndN) -- Proof
    xs_multnils <- combine xs multnils
    c::maybexs_maybenils <- controlUST c (xs_multnils) (swapRegistersByLength {n = (S h) + (S h)} {i = S h} {j = S h})
    maybexs # maybenils <- splitQubitsInto (S h) (S h) maybexs_maybenils
    (c::ancilla::all) # finalb <- (cMultAModN [c] [ancilla] (maybexs) (asmodinv) (rewrite sym $ minusminusplusplusSH {h = h} in bigNs) (ovf::maybenils)) -- Proof 
    pure $ (++) (c::ancilla::all) as # finalb

-- Now, as per Beauregard, we can classically calculate a^n mod N (see implementation above as illustration), and feed that in instead of a
-- therefore, we are done

---------------MODULAR EXPONENTIATION---------------

--This then is just calling the modular multiplication with a = a^n, and a^(-1) mod N = a^n^(-1) mod N.
-- What we do want, however, is to move the output, which is in x, into one of the output vectors by itself, as opposed to bs, this time
export
inPlaceModularExponentiation: UnitaryOp t => {i: Nat} -> {n : Nat}
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect i Qubit) -- this is x represented in j qubits
                                -> (1 an : LVect i Qubit) -- this is a^n represented in i qubits
                                -> (1 anmodinv : LVect i Qubit) -- this is a^n^(-1) mod N represented in i qubits. The classical algorithm for calculating this
                                                        -- from a is included above given the theoretical assurances in Beuregard
                                                        -- Note that since the content of the registers has to be prepared elsewhere, this is perfectly fine to assume
                                -> (1 bigN  : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 nils : LVect (S i) Qubit) -- this should be |0>(S n) because we are actually trying to calculate (ax mod N)
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (3 + i + i + i + i) Qubit) (LVect (i) Qubit))
inPlaceModularExponentiation [c] [ancilla] [] [] [] [] [q] = pure $ [c,ancilla,q] # []
inPlaceModularExponentiation [_] [_] [] [] [] [] [] impossible
inPlaceModularExponentiation {i = S h} [c] [ancilla] (xs) (ans) (asnmodinv) (bigNs) (nils) = do
    (rest) # (ovf::bs) <- inPlaceModExp [c] [ancilla] (xs) (ans) (asnmodinv) (bigNs) (nils)
    (c::ancilla::xs) # restrest <- splitQubitsInto {prf = plusSheq h} (S (S (S h))) (plus (plus (S h) (S h)) (S h)) rest
    all <- combine {i = S h} bs restrest
    finall <- combine {i = 3} (c::ancilla::[ovf]) (all)
    (pure $ (rewrite sym $ plusthreeSeq h in finall) # xs) -- IF the types are given carefully, then this proof is unnecessary! See below.

---------------MODULAR EXPONENTIATION No PRF---------------

inPlaceModularExponentiationNoPrf: UnitaryOp t => {i: Nat} -> {n : Nat}
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect i Qubit) -- this is x represented in j qubits
                                -> (1 an : LVect i Qubit) -- this is a^n represented in i qubits
                                -> (1 anmodinv : LVect i Qubit) -- this is a^n^(-1) mod N represented in i qubits. The classical algorithm for calculating this
                                                        -- from a is included above given the theoretical assurances in Beuregard
                                                        -- Note that since the content of the registers has to be prepared elsewhere, this is perfectly fine to assume
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 nils : LVect (S i) Qubit) -- this should be |0>(S n) because we are actually trying to calculate (ax mod N)
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (S (S (S (i + (i + i + i))))) Qubit) (LVect (i) Qubit) )
inPlaceModularExponentiationNoPrf [c] [ancilla] [] [] [] [] [q] = pure $ [c,ancilla,q] # []
inPlaceModularExponentiationNoPrf [_] [_] [] [] [] [] [] impossible
inPlaceModularExponentiationNoPrf {i = S h} [c] [ancilla] (xs) (ans) (asnmodinv) (bigNs) (nils) = do
    (rest) # (ovf::bs) <- inPlaceModExp [c] [ancilla] (xs) (ans) (asnmodinv) (bigNs) (nils)
    (c::ancilla::xs) # restrest <- splitQubitsInto {prf = plusSheq h} (S (S (S h))) (plus (plus (S h) (S h)) (S h)) rest
    all <- combine {i = S h} bs restrest
    finall <- combine {i = 3} (c::ancilla::[ovf]) (all)
    (pure $ (finall) # xs)


--------------- Basic encoding on natural numbers  into register of size i --------------   

data Bit : Type where 
    B0 : Bit
    B1 : Bit

partial
||| this shouldnt ever get inputs other than zero or one - idris unfortunately cannot recognize that there will be no other cases
mod2toBin : Nat -> Bit
mod2toBin any = case mod any 2 of 
    Z => B0
    (S Z) => B1


partial
||| this is in fact total, but the compiler does not recognize it
natToBinList : (num : Nat) -> List Bit
natToBinList Z = [B0]
natToBinList (S Z) = [B1]
natToBinList (S (S n)) = natToBinList (divNat (S (S n)) 2) ++ [mod2toBin (S (S n))]


||| Take i elements from a list of Bits and turn them into a vector. 
||| If the lest is empty, then we pas with zeros to the LEFT
takeiBitListtoVectPadLeft : (i: Nat) -> List Bit -> Vect i Bit
takeiBitListtoVectPadLeft Z any = []
takeiBitListtoVectPadLeft (S k) [] = rewrite sym $ lemmaplusOneRight k in takeiBitListtoVectPadLeft k [] ++ [B0] -- if the list does not contain bits, then the recovered value is zero
takeiBitListtoVectPadLeft (S k) (x::xs) = x :: (takeiBitListtoVectPadLeft  k xs)

partial
||| This is UNSAFE for convenience. Collects on the left.
natToBinIVect : (i: Nat) -> (num:Nat) -> Vect i Bit
natToBinIVect Z _ = []
natToBinIVect (S i) Z = takeiBitListtoVectPadLeft (S i) (natToBinList Z)
natToBinIVect (S i) (S n) = takeiBitListtoVectPadLeft (S i) (natToBinList (S n))

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

partial -- because mod2ToBin is partial, and therefore natToBinList is partial, therefore natToBinIVect is partial. Could be made total.
||| Takes a Nat and a vector of qubits expected to be in |0>^n, and returns the unitary operation of encoding the number in the qubits
||| It will truncate the number if the qubits are not enoguh to contain it, otherwise it will pad
natToUnitaryI : UnitaryOp t => {i:Nat} -> {n:Nat} -> (num:Nat) -> (1_ : LVect i Qubit) -> UStateT (t n) (t n) (LVect i Qubit)
natToUnitaryI _ [] = pure []
natToUnitaryI Z (q::qs) = pure (q::qs)
natToUnitaryI {i = (S k)} (S n) (q::qs) = binVectToUnitaryI (natToBinIVect (S k) (S n)) (q::qs)

partial export
||| modular exponentiation using QuantumOp and UnitaryOp
modularExponentiationOp: QuantumOp t => UnitaryOp t => 
                                                     (1_ : LVect 1 Qubit) -- the control, comes from a different computation, 
                                                    -> (i:Nat) -> (n:Nat) -> (x : Nat) -> (a:Nat) -> (bigN: Nat)
                                                    -> QStateT (t 1) (t (2 + i + i + i + i + (S i))) ((LVect (3 + i + i + i + i + i) Qubit))
modularExponentiationOp {t = t} c i n x a bigN = let 
                                          an = power a n 
                                          anmodinv = modInverse an
                                        in
                                            do 
                                                ancilla <- newQubit {t = t} 
                                                xs0 <- newQubits {t = t} i
                                                xs <- applyUST {t = t} (natToUnitaryI x xs0)
                                                asn0 <- newQubits {t = t} i
                                                asn <- applyUST {t = t} (natToUnitaryI x asn0)
                                                asmodinv0 <- newQubits {t = t} i
                                                asmodinv <- applyUST {t = t} (natToUnitaryI x asmodinv0) 
                                                bigNs0 <- newQubits {t = t} i
                                                bigNs  <- applyUST {t = t} (natToUnitaryI x bigNs0)
                                                bsZeros <- newQubits {t = t} (S i)
                                                output <- applyUST (combineAbs $ inPlaceModularExponentiation c [ancilla] xs asn asmodinv bigNs bsZeros)
                                                pure (output)
                                                      
-------------------- Unitary part of QME test --------------------------
%hint
||| this is rather anoyingly needed for below; an alternative is 
||| what is done for the algorithm with unitary reuse: a single input vector.
natplusS : {n:Nat} -> Prelude.S (Prelude.S (plus (plus (plus (plus (plus 0 n) n) n) n) n)) = Prelude.S (plus (plus (plus (plus (plus 0 n) n) n) n) (Prelude.S n))
natplusS {n} = rewrite plusSuccRightSucc ((plus (plus (plus (plus 0 n) n) n) n)) n in Refl


export
modularN : {n:Nat} -> Unitary (S (S (plus (plus (plus (plus (plus 0 n) n) n) n) (S n))))
modularN {n} = runUnitaryOp {t=Unitary} (do
        c <- supplyQubits 1--- recall that UnitaryOp can only ever get qubits from quantumOp, so we dont have to worry about whether the qubits will be distinct
        ancilla <- supplyQubits 1
        ans <- supplyQubits n
        xs <- supplyQubits n
        asnmodinv <- supplyQubits n
        bigNs <- supplyQubits n
        nils <- supplyQubits (S n)
        out <-  applyUStateT (combineAbs $ inPlaceModularExponentiation c ancilla (xs) (ans) (asnmodinv) (bigNs) (nils))
        pure (rewrite sym $ natplusS {n = n} in out))


||| testing the unitary part of modular exponentiation
export
modularTestSmall : (Unitary 8)
modularTestSmall = modularN {n = 1}

||| Larger test (takes a while)
export
modularTest : (Unitary 33)
modularTest = modularN {n = 6}
        
        
modularTestGateCount: List Nat
modularTestGateCount = let gate = modularTest in
    let gates = gateCount gate 
        hs = Hcount gate
        ps = Pcount gate
        cnots = CNOTcount gate
        in [gates, hs, ps, cnots]

        
modularTestOpt : Nat
modularTestOpt = gateCount (optimise modularTest)


{-
 modularTestGateCount 
[887836, 
122212, 
430104, 
335520]
-}

--------- IN-PLACE MODULAR EXPONENTIATION : Reduced Recomputation ------------       
||| due to the monadic style being very computationally intensive, 
||| this does not actually help us too much.
||| Idris frequently does this by itself if we use applyUnitary
||| and outside definitions that are identical; this way, we enforce it
-----------------------------------------------------------------------------

export
inPlaceModularAdderFast :  UnitaryOp t => {i: Nat} -> {n : Nat} 
                                -> (1 controls : LVect 2 Qubit) -- these are the controls c1 and c2
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla
                                -> (1 a : LVect i Qubit) -- this is a represented in i Qubits
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i Qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) (LVect (3 + i + i + (S i)) Qubit) -- we collect the 2 controls, ancilla, a, and N in the same output LVect, and b in the other

inPlaceModularAdderFast [c1,c2] [ancilla] [] [] [q] = pure $ (c1::c2::ancilla::[q])
inPlaceModularAdderFast {i = S k} {n} [c1,c2] [ancilla] (a::as) bigNs (b::bs) = 
    let qftadder = (buildUnitary {t = Unitary} (inPlaceQFTAdder  {n = S k + S (S k)} {i = S k})) in
    let qftadderInv = buildUnitary {t = Unitary} (inPlaceQFTAdderInv {n = S k + S (S k)} {i = S k}) in
    let qft = buildUnitary {t = Unitary} (qft {n = S (S k)}) in
    let revqft = adjoint qft in
    do
    asbs <- combine (a::as) (b::bs)
    (c1::c2::asbs)<- applyUnitary (c1::c2::asbs) (multipleControlled 2 qftadder)
    as # bs <- splitQubitsInto (S k) (S (S k)) asbs
    bigNsbs <-   applyUnitary (bigNs++bs) qftadderInv
    bigNs # bs <- splitQubitsInto (S k) (S (S k)) bigNsbs
    (s::qibs) <-  applyUnitary (bs) revqft-- the most signigifact bit in out case will be the first, which is where the overflow goes, so this is our control
    [s,ancilla] <- applyCNOT s ancilla
    invqftbs <-  applyUnitary (s::qibs) qft
    toAddInv <- combine bigNs invqftbs
    ancilla::bigNs_bs <- applyUnitary (ancilla::toAddInv) (controlled qftadderInv)
    bigNs # bs <- splitQubitsInto (S k) (S (S k)) bigNs_bs
    asbs <- combine (as) (bs)
    (c1::c2::asbs) <-  applyUnitary (c1::c2::asbs) (multipleControlled 2 qftadder)
    as # bs <- splitQubitsInto (S k) (S (S k)) asbs
    (s::qibs) <-   applyUnitary (bs) revqft
    [s] <- applyUnitary [s] XGate
    [s,ancilla] <- applyCNOT s ancilla
    [s] <- applyUnitary [s] XGate
    qftbs <-  applyUnitary (s::qibs) qft
    asbs <- combine (as) (qftbs)
    (c1::c2::asbs) <-  applyUnitary (c1::c2::asbs) (multipleControlled 2 qftadder)
    as # bs <- splitQubitsInto (S k) (S (S k)) asbs
    aAndN <- combine as bigNs
    aAndNAndB <- combine  aAndN bs
    pure $ ((++) (c1::c2::[ancilla]) aAndNAndB)


inPlaceModularAdderSingle : UnitaryOp t => {i: Nat} -> {n : Nat} -> (1 qubits: LVect ((3 + i + i + (S i))) Qubit) -- these are the controls c1 and c2
                               -> UStateT (t (S (S n))) (t (S (S n))) ((LVect (3 + i + i + (S i)) Qubit))
inPlaceModularAdderSingle {i} qs = do
    [c1,c2,anc] # rest1 <- splitQubitsInto 3 (i + i + (S i)) qs
    a # rest2 <- splitQubitsInto i (i+(S i)) (rewrite plusAssociative' i i (S i) in rest1)
    bigN # b <- splitQubitsInto i ((S i)) rest2
    out <- inPlaceModularAdderFast [c1,c2] [anc] a bigN b
    pure out

||| Helper function that does the reursion on x, using each bit as control. 
allControlsFast:  UnitaryOp t => {j:Nat} -> {i: Nat} -> {n : Nat} -> {auto prf: LTE j i} -- This is somewhat superfluous, because we can handle other inputs as well it just won't make sense anyway. if we remove this there is only 1 proof required
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect j Qubit) -- this is x represented in j qubits
                                -> (1 a : LVect i Qubit) -- this is a represented in i qubits
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> (adder: Unitary (2 + 1+ i+ i +(S i))) -- adder supplied as tn from cMult
                                -> UStateT (t (S (S n))) (t (S (S n))) (LPair (LVect (2 + j + i + i)  Qubit) (LVect ((S i)) Qubit))
allControlsFast [c] [ancilla] [] [] [] q adder= pure $ [c, ancilla] # q
allControlsFast [_] [_] [] (x :: xs) (ns::bigNs) [] adder impossible -- for some reason idris wants this case
allControlsFast [c] [ancilla] (x:: xs) [] [] [q] adder impossible -- because of the way b is set up, the control wont be relevant for the additiona qubit anywa; this should not happen (condition LT j i is excluded for simplicity)
allControlsFast [c] [ancilla] (x::xs) [] [] [q] adder impossible -- for some reason, needs separate case
allControlsFast [c] [ancilla] [] (a::as) (ns::bigNs) (b::bs) adder = do ---for some reason, idris needs the (::) operators here to recognize coverage, again...
    aAndN <- combine (a::as) (ns::bigNs)
    pure $ ((++) (c::[ancilla]) aAndN) # (b::bs)
allControlsFast {prf} {j = S r} {i = S h} [c] [ancilla] (x::xs) a bigNs b adder = do
    cxa <- combine ([c,x]) [ancilla]
    aAndN <- combine a bigNs
    firsts <- combine cxa aAndN
    toadd <- combine firsts b
    (c::x::ancilla::aAndNAndB) <- applyUnitary toadd adder
    aAndN # bs <- splitQubitsInto (S h + S h) ((S (S h))) aAndNAndB -- the compiler sometimes finds this sometimes doesnt {prf = lteSiPlusSi} 
    a # bigNs <- splitQubitsInto (S h) ((S h)) aAndN
    (c::ancilla::all) # finalb <- allControlsFast {j = r} {i = S h} {prf = fromLteSucc $ lteSuccRight prf} [c] [ancilla] (xs) a (bigNs) bs adder---ONE PROOF is necessary, the other depends on the LT condition
    pure $ (c::ancilla::x::all) # finalb 

adder :  UnitaryOp t => (i:Nat) -> t (3 + i + i + (S i))
adder i = buildUnitary {n = (3 + i + i + (S i))} (inPlaceModularAdderSingle {i = i} )


|||Intermediaty multiplication function, output is (b+ax) mod N if c=1 else b
cMultAModNFast:  UnitaryOp t => {i: Nat} -> {n : Nat}
                                -> (1 c : LVect 1 Qubit) -- this is the control c
                                -> (1 ancilla : LVect 1 Qubit) -- this is the additional ancilla for the addition operation
                                -> (1 x : LVect i Qubit) -- this is x represented in i qubits 
                                -> (1 a : LVect i Qubit) -- this is a represented in i qubits
                                -> (1 bigN : LVect i Qubit) -- this is N represented in i qubits
                                -> (1 b : LVect (S i) Qubit) -- this is b plus the required additional qubit as the last qubit
                                -> UStateT (t (S (S n))) (t (S (S n))) ((LVect (2 + i + i + i + S i) Qubit))
cMultAModNFast [c] [ancilla] [] [] [] [q] = pure $ [c,ancilla,q]
cMultAModNFast [_] [_] [] [] [] [] impossible
cMultAModNFast {i = S k} [c] [ancilla] (xs) (as) (bigNs) (bs) = 
    let qft = buildUnitary {t = Unitary} (qft {n = S (S k)}) in
    let revqft = adjoint qft in
    let adder = adder {t = Unitary} (S k) in
    do
    qftb <- applyUnitary (bs) qft
    middleAll # middleB <- allControlsFast [c] [ancilla] (xs) (as) (bigNs) qftb adder
    finalB <-  applyUnitary middleB revqft
    pure $ middleAll ++ finalB


cMultAModNSingle :  UnitaryOp t => {i: Nat} -> {n : Nat} -> (1 qubits: LVect ((2 + i + i + i + (S i))) Qubit) -- these are the controls c1 and c2
                               -> UStateT (t (S (S n))) (t (S (S n))) ((LVect (2 + i + i + i + (S i)) Qubit))
cMultAModNSingle {i} qs = do
    [c1,c2] # rest <- splitQubitsInto 2 (i + i + i + (S i)) qs
    x # rest1 <- splitQubitsInto i (i + i + (S i)) (rewrite plusAssociative' i (i+i) (S i) in rewrite plusCommutative' i (i+i) in rest)
    a # rest2 <- splitQubitsInto i (i+(S i)) (rewrite plusAssociative' i i (S i) in rest1)
    bigN # b <- splitQubitsInto i ((S i)) rest2
    out <- cMultAModNFast [c1] [c2] x a bigN b
    pure (out)

cmult :  UnitaryOp t => (i:Nat) -> t (2 + i + i + i + (S i))
cmult i = buildUnitary {n = (2 + i + i + i + (S i))} (cMultAModNSingle {i = i} )   

|||in place modular multiplication function
inPlaceModExpFast:  UnitaryOp t => {i: Nat} -> {n : Nat}
                                -> (1 amodinv : LVect i Qubit)
                                -> (1 all: LVect (2 + i + i + i + (S i)) Qubit)
                                -> UStateT (t (S (S n))) (t (S (S n))) ((LVect (2 + i + i + i +(S i) + i)) Qubit) -- this time x contains the computationally relevant bit so that is given back separately
inPlaceModExpFast [] [c,ancilla, q] = pure $ [c,ancilla,q]
inPlaceModExpFast {i = S h} (asmodinv) all = 
    let cmultmod = cmult {t = Unitary} (S h) in
    do
    (c::ancilla::rest) <-  applyUnitary all cmultmod
    cmulted # (ovf::multnils) <- splitQubitsInto ((S h) + (S h) + (S h)) (S (S h)) rest
    xs # aAndN <- splitQubitsInto (S h) (S h + S h) (rewrite plusAssociative' (S h) (S h) (S h) in cmulted) -- Proof 
    as # bigNs <- (splitQubitsInto (S h) (S h) aAndN) -- Proof
    xs_multnils <- combine xs multnils
    c::maybexs_maybenils <- controlUST c (xs_multnils) (swapRegistersByLength {n = (S h) + (S h)} {i = S h} {j = S h})
    maybexs # maybenils <- splitQubitsInto (S h) (S h) maybexs_maybenils
    xsmod <- combine maybexs asmodinv
    left <- combine xsmod bigNs
    all <- combine left (ovf::maybenils)
    (c::ancilla::rest) <- applyUnitary (c::ancilla::all) cmultmod-- Proof 
    pure $ ((c::ancilla::rest) ++ as)


---For this development, we won't reorder the qubits, we will just buildinPlaceModExpFast: UnitaryOp t => {i: Nat} -> {n : Nat}
inPlaceModSingle :  UnitaryOp t => {i: Nat} -> {n : Nat} -> (1 qubits: LVect (2 + i + i + i + (S i) + i) Qubit)
                 -> UStateT (t (S (S n))) (t (S (S n))) ((LVect (2 + i + i + i +(S i) + i)) Qubit) -- this time x contains the computationally relevant bit so that is given back separately
inPlaceModSingle qs = do
    rest # asmodinv <- splitQubitsInto ( 2 + i + i + i + (S i)) i qs
    out <- inPlaceModExpFast asmodinv rest
    pure out

export
modUTest : (i:Nat) -> Unitary (2 + i + i + i +(S i) + i)
modUTest i = buildUnitary {t = Unitary} inPlaceModSingle



       