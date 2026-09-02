module Lemmas

import Data.Nat
import Data.Vect
import Data.Fin
import Decidable.Equality
import Injection
import Complex
import NatRules
import LinearTypes
import public Data.Linear.Notation
import public Data.Linear.Interface
import System
import Data.Linear


%default total

%search_timeout 1000

---------------- Restatements of some library functions idris cannot find ----------------------

export
%hint
lemmaplusOneRight : (n : Nat) -> n + 1 = S n
lemmaplusOneRight n = rewrite plusCommutative n 1 in Refl

export
%hint
lemmaplusOneRightHC : {n : Nat} -> n + 1 = S n
lemmaplusOneRightHC {n = n} = rewrite plusCommutative n 1 in Refl

export
%hint
lemmaplusOneRightH : {n : Nat} -> 1 + n = S n
lemmaplusOneRightH {n = n} = Refl

export
%hint
lemmaplusOneLeft : (n : Nat) -> 1 + n = S n
lemmaplusOneLeft n = Refl

export
%hint
lemmaplusOneLeftsym : (n : Nat) -> S n = 1 + n 
lemmaplusOneLeftsym n = Refl

export
%hint
lemmaplusOneRightHSym : {n : Nat} ->  S n = n + 1 
lemmaplusOneRightHSym {n = n} = sym $ rewrite plusCommutative n 1 in Refl

export
%hint
lemmaplusOneRightHSymExp : (n : Nat) ->  S n = n + 1 
lemmaplusOneRightHSymExp n = lemmaplusOneRightHSym {n = n}


export
%hint
lemmaPlusSRight : (n : Nat) -> (k : Nat) -> plus n (S k) = S (plus n k)
lemmaPlusSRight Z     k = Refl
lemmaPlusSRight (S p) k = rewrite lemmaPlusSRight p k in Refl

export 
%hint
sPlusEq : {k:Nat} -> {m:Nat} -> S (plus k m) = plus k (S m)
sPlusEq {k=k} {m=m} = rewrite plusSuccRightSucc k m in Refl

--restatement of mirror locally 
export
mirror : Either a b -> Either b a
mirror (Left  x) = Right x
mirror (Right x) = Left x

--successives of LT inside Either
eitherLTSucc :{a,b:Nat} -> Either (LT (S a) (S b)) (LT (S b) (S a)) -> Either (LT a b) (LT b a)
eitherLTSucc (Left a) = Left (fromLteSucc a)
eitherLTSucc (Right b) = Right (fromLteSucc b)

eitherLTtoSucc : Either (LT a b) (LT b a) -> Either (LT (S a) (S b)) (LT (S b) (S a))
eitherLTtoSucc (Left a) = Left (LTESucc a)
eitherLTtoSucc (Right b) = Right (LTESucc b)

eqVoidSucc :{a,b:Nat} -> ((S a) = (S b) -> Void) -> ((a = b) -> Void)
eqVoidSucc ltToVoid Refl = ltToVoid Refl

--LEMMAS ABOUT &&

export
lemmaAndLeft : {a : Bool} -> {b : Bool} -> (a && b = True) -> (a = True)
lemmaAndLeft {a = True} {b} p =  Refl
lemmaAndLeft {a = False} {b} p impossible

export
lemmaAndRight : {a : Bool} -> {b : Bool} -> (a && b = True) -> (b = True)
lemmaAndRight {a} {b = True} p = Refl
lemmaAndRight {a = True} {b = False} p impossible
lemmaAndRight {a = False} {b = False} p impossible

export
lemmaAnd : {a : Bool} -> {b : Bool} -> (a = True) -> (b = True) -> (a && b = True)
lemmaAnd {a = True} {b = True} p1 p2 = Refl



--BASIC LEMMAS ABOUT <, >, =, /=, <=, >=

export
||| `LTE` is reflexive.
lteRefl : (n:Nat) -> LTE n n
lteRefl Z   = LTEZero
lteRefl (S k) = LTESucc (lteRefl k)

export
%hint
lteReflHint : {n:Nat} -> LTE n n
lteReflHint {n} = lteRefl n 

export
lemmaLTERefl : (n : Nat) -> LTE n n
lemmaLTERefl any = lteRefl any

export
lemmaSymDiff : {x : Nat} -> {y : Nat} -> (x /= y) = True -> (y /= x) = True
lemmaSymDiff {x = 0} {y = (S m)} _ = Refl
lemmaSymDiff {x = (S k)} {y = 0} _ = Refl
lemmaSymDiff {x = (S k)} {y = (S j)} prf = lemmaSymDiff {x = k} {y = j} prf


export 
%hint
lemma1LTESucc : (k : Nat) -> LTE 1 (S k)
lemma1LTESucc 0 = lteRefl 1
lemma1LTESucc (S k) = lteSuccRight $ lemma1LTESucc k

export 
%hint
lemma0LTSucc : (k : Nat) -> LT 0 (S k)
lemma0LTSucc Z = lteRefl 1
lemma0LTSucc (S k) = lteSuccRight $ lemma0LTSucc k


export 
%hint
lemmaLTEAddR : (n : Nat) -> (p : Nat) -> LTE n (n+p)
lemmaLTEAddR Z 0 = lteRefl Z
lemmaLTEAddR Z (S k) = LTEZero
lemmaLTEAddR (S n) p = LTESucc $ lemmaLTEAddR n p

export 
%hint
lemmaLTEAddL : (n : Nat) -> (p : Nat) -> LTE p (plus n p)
lemmaLTEAddL n p = rewrite plusCommutative n p in lemmaLTEAddR p n


export 
%hint
lemmaDiffSuccPlus : (k : Nat) -> (p : Nat) -> (k /= S (p + k)) = True
lemmaDiffSuccPlus 0 p = Refl
lemmaDiffSuccPlus (S k) j = rewrite sym $ plusSuccRightSucc j k in lemmaDiffSuccPlus k j

export 
%hint
lemmaLTSuccPlus : (k : Nat) -> (p : Nat) -> LT k (S (k+p))
lemmaLTSuccPlus 0 0 = lteRefl 1
lemmaLTSuccPlus 0 (S j) = lteSuccRight $ fromLteSucc $ LTESucc $ lemmaLTSuccPlus 0 j
lemmaLTSuccPlus (S k) j = LTESucc $ lemmaLTSuccPlus k j

export 
%hint
lemmaLTSucc : (k : Nat) -> LT k (S k)
lemmaLTSucc 0 = lteRefl 1
lemmaLTSucc (S k) = LTESucc $ lemmaLTSucc k

export 
%hint
lemmakLTSk : (k : Nat) -> LT (S k) (S (k+1))
lemmakLTSk k = rewrite lemmaplusOneRight k in (LTESucc $ lemmaLTSucc k)

export 
lemmaLTSuccLT : (k : Nat) -> (n : Nat) -> LT (S k) n -> LT k n
lemmaLTSuccLT k 0 prf impossible
lemmaLTSuccLT 0 n prf = fromLteSucc $ lteSuccRight prf
lemmaLTSuccLT (S k) (S n) prf = lteSuccLeft prf


||| Slows down compilation significantly if made into a hint!
export 
lemmaLTSuccLTH : {k : Nat} -> {n : Nat} -> LT (S k) n -> LT k n
lemmaLTSuccLTH {k = k} {n = 0} prf impossible
lemmaLTSuccLTH {k = 0} {n = n} prf = fromLteSucc $ lteSuccRight prf
lemmaLTSuccLTH {k = (S k)} {n = (S n)} prf = lteSuccLeft prf

export 
%hint
lemmaLTESuccLT : (k : Nat) -> (n : Nat) -> LTE (S k) n -> LT k n
lemmaLTESuccLT k 0 prf impossible
lemmaLTESuccLT 0 n prf = prf
lemmaLTESuccLT (S k) (S j) prf = prf

||| Slows down compilation significantly if made into a hint!
export 
lemmaLTESuccLTE : (k : Nat) -> (n : Nat) -> LTE (S k) n -> LTE k n
lemmaLTESuccLTE k 0 prf impossible
lemmaLTESuccLTE 0 _ _ = LTEZero
lemmaLTESuccLTE (S k) (S j) prf = lteSuccLeft prf

export 
%hint
lemmaSuccsLT : (k : Nat) -> (n : Nat) -> LT (S k) (S n) -> LT k n
lemmaSuccsLT k n prf = fromLteSucc prf

export 
%hint
lemmaCompLT0 : (n : Nat) -> (j : Nat) -> {auto prf : LT j n} -> LT 0 n
lemmaCompLT0 n 0 {prf} = prf
lemmaCompLT0 p (S k) {prf} = lemmaCompLT0 p k {prf = fromLteSucc $ lteSuccRight prf}

---------------- Lemmas about + (some are library functon restatements)---------------------


export 
plusSuccLeftSucc : (left, right : Nat) -> S (left + right) = (S left) + (right)
plusSuccLeftSucc l r = rewrite plusCommutative l r in Refl

export
plusSuccLeftRight : (left, right : Nat) -> (S left + right) = (left) + (S right)
plusSuccLeftRight l r = rewrite plusCommutative (S l) (r) in rewrite sym $ sPlusEq {k = r} {m = l} in 
                        rewrite plusCommutative r l in rewrite sPlusEq {k=l} {m=r} in Refl

plusSuccLeftisSuccRight : (left, right : Nat) -> (S left) + (right) = (left) + (S right)
plusSuccLeftisSuccRight left right = rewrite plusSuccLeftSucc left right in (rewrite sym $ plusSuccLeftRight left right in Refl)

export 
%hint
lteSAssoc : {k:Nat} -> LT (S (S k)) (S k + 1) -> LT (S (S k)) (S (k + 1))
lteSAssoc lte = %search

export
%hint
succkplus : {k:Nat} -> (S (k + 1)) = (S k + 1)
succkplus = %search

export 
%hint
lteSS : {k:Nat} -> LTE (S (S k)) (S k + 1)
lteSS {k} = rewrite succkplus {k = k} in lemmakLTSk k

||| Succ is injective - library function
export
succInjective : {left, right : Nat} -> S left = S right -> left = right
succInjective Refl = Refl

export
ltekplusk : {k:Nat} -> LTE k (k + k)
ltekplusk {k} = lemmaLTEAddR k k

export
plusk2 : {k:Nat} -> (plus k 2) = S ( S k)
plusk2 = rewrite sym $ plusOneSucc (k) in (rewrite plusCommutative 1 k in (rewrite sym $ plusSuccRightSucc (k) 1 in Refl))

export
lteSk : {k:Nat} -> LTE (S k) (S k + (S k))
lteSk = ltekplusk {k = (S k)}

export
lteSSk : {k:Nat} -> LTE (S (S k)) (S (S k + (S k)))  
lteSSk = LTESucc (lteSk {k = k})

export
lteSkS : {k:Nat} -> LTE (S (S k)) (S k + S (S k)) 
lteSkS = rewrite sym $ plusSuccRightSucc (S k) (S k) in (lteSSk {k = k})

export
%hint
lte2ks : {k:Nat} -> LTE (S (S (S ( S k)))) (S (S (S k + S (S k))))
lte2ks = LTESucc $ LTESucc $ lteSkS {k = k}

export 
%hint
lteplus2s : {k:Nat} -> LTE (S (S (plus k 2))) (S (S (S k + S (S k))))
lteplus2s {k} = rewrite plusk2 {k = k} in lte2ks {k = k}

export
minuspluszerore : {left: Nat} -> {right: Nat} -> minus (plus (left + 0) right) (left + 0) = minus (plus (left) right) (left + 0)
minuspluszerore = rewrite plusZeroRightNeutral left in Refl


export
%hint
lteSiPlusi: {i:Nat} -> LTE (S i) (S (plus i i))
lteSiPlusi = LTESucc ltekplusk

export
%hint
lteSiPlusik: {i:Nat} -> {k:Nat} -> LTE (S i) (S (plus i k))
lteSiPlusik {i} {k} = LTESucc $ lemmaLTEAddR i k 

export
%hint
lteSiPlusSi: {i:Nat} -> LTE (S (S i)) (S (plus i (S i)))
lteSiPlusSi = rewrite sym $ plusSuccRightSucc i i in LTESucc $ lteSiPlusi

export
%hint
lteSiPlusSik: {i:Nat} -> {k:Nat} -> LTE (S (S i)) (S (plus i (S k)))
lteSiPlusSik = rewrite sym $ plusSuccRightSucc i k in LTESucc $ lteSiPlusik

export
lteSiPlusPlusSiHelp: {i:Nat} -> {k:Nat} -> LTE (S (S (plus i (S i)))) (S (plus (plus i (S i)) (S k)))
lteSiPlusPlusSiHelp {i} {k} = lteSiPlusSik {i = plus i (S i)} {k = k}

export
%hint
lteSiPlusPlusSi: {i:Nat} -> LTE (S (S i)) (S (plus (plus i (S i)) (S i)))
lteSiPlusPlusSi = lteTransitive (lteSiPlusSik {i=i} {k=i}) (lteSuccLeft $ lteSiPlusPlusSiHelp {i=i} {k=i})


public export
plusMinusLeftCancel0 : (left, right : Nat)  ->
  minus (plus left right) (left) = right
plusMinusLeftCancel0 left right = rewrite sym $ plusZeroRightNeutral left in (rewrite minuspluszerore {left = left} {right = right} in (rewrite plusMinusLeftCancel left right 0 in (rewrite minusZeroRight right in Refl)))

public export
%hint
plusMinusLeftCancel0H : {left, right : Nat} ->
  minus (plus left right) (left) = right
plusMinusLeftCancel0H {left} {right} = plusMinusLeftCancel0 left right

export
minplusrewrite1 : {h:Nat} -> (minus (plus (plus h (S h)) (S h)) h) = (minus (plus (S h) ((plus h (S h)))) h)
minplusrewrite1 {h} = rewrite plusCommutative (plus h (S h)) (S h) in Refl

export
minplusrewrite2 : {h:Nat} -> (minus (plus (S h) ((plus h (S h)))) h) = (minus (plus (S h) (S (plus h (h)))) h)
minplusrewrite2 {h} = rewrite lemmaPlusSRight h h in Refl

export
minplusrewrite3 : {h:Nat} -> (minus (plus (S h) (S (plus h (h)))) h) = (minus (plus (h) (S (S (plus h (h))))) h)
minplusrewrite3 {h} = rewrite plusSuccLeftRight h (S (plus h (h))) in Refl

export
lteSSplusHH : {h : Nat} -> LTE (S (S h)) (S (S (plus h (h))))
lteSSplusHH {h} = LTESucc lteSiPlusi 

export
plusMinusLeftCancelDeep : {h:Nat} ->  LTE (S (S h)) (minus (plus (plus h (S h)) (S h)) h)
plusMinusLeftCancelDeep {h} = rewrite minplusrewrite1 {h = h} in (rewrite minplusrewrite2 {h = h} in (
                              rewrite minplusrewrite3 {h = h} in (rewrite plusMinusLeftCancel0 h (S (S (plus h h))) in lteSSplusHH)))

export                            
minusminusplusplusSH : {h:Nat} -> minus (minus (plus (plus h (S h)) (S h)) h) (S h) = S h          
minusminusplusplusSH = rewrite minplusrewrite1 {h = h} in (rewrite minplusrewrite2 {h = h} in (
                       rewrite minplusrewrite3 {h = h} in (rewrite plusMinusLeftCancel0 h (S (S (plus h h))) in 
                       (rewrite plusSuccRightSucc h h in (rewrite plusMinusLeftCancel0 h (S h) in Refl)))))
export
veryLongPlusMinus : {h: Nat} -> plus (minus (plus (plus h (S h)) (S h)) h) (S (S h)) = S (plus (plus h (S h)) (S (S h)))
veryLongPlusMinus {h} = rewrite minplusrewrite1 {h = h} in (rewrite minplusrewrite2 {h = h} in (
                       rewrite minplusrewrite3 {h = h} in (rewrite plusMinusLeftCancel0 h (S (S (plus h h))) in 
                       (rewrite sym $ plusSuccRightSucc h h in Refl))))

export                      
ltesss : (h:Nat) -> LTE (S (S (S (S h)))) (S (S (S (((h + (S h)) + (S h)) + (S h)))))
ltesss h = LTESucc $ LTESucc $ LTESucc $ lemmaLTEAddL ((h + (S h)) + (S h)) (S h)
--(S (S (S (plus (plus k (minus (plus (plus k (S k )) (S k )) k )) (S (S k )))))) rewrite sym $ plusSuccRightSucc (plus (plus h (S h)) (S h)) h in 

export 
mpppss : (h:Nat) -> minus(plus (plus (plus h (S h)) (S h)) (S h)) h = S (plus (plus h (S h)) (S h))
mpppss h = rewrite plusCommutative (plus (plus h (S h)) (S h)) (S h) in (rewrite plusSuccLeftisSuccRight h (plus (plus h (S h)) (S h)) in 
            rewrite plusMinusLeftCancel0 h (S (plus (plus h (S h)) (S h))) in Refl)

export            
plusSheq : (h:Nat) -> plus (S (S (S h))) (S (plus (plus h (S h)) (S h))) = S (S (S (plus (plus (plus h (S h)) (S h)) (S h))))
plusSheq h = rewrite plusSuccLeftSucc ((S (S h))) (S (plus (plus h (S h)) (S h))) in 
             rewrite plusSuccLeftSucc (((S h))) (S (plus (plus h (S h)) (S h))) in
             rewrite plusSuccLeftSucc (((h))) (S (plus (plus h (S h)) (S h))) in 
             rewrite plusCommutative (plus (plus h (S h)) (S h)) (S h) in 
             rewrite plusSuccRightSucc' h (plus (plus h (S h)) (S h)) in Refl 

export
plusSSeq : (h:Nat) ->  (S (S (S (S (plus (plus (plus h (S h)) (S h)) (S h)))))) = S (S (S (plus (plus (plus (S h) (S h)) (S h)) (S h))))
plusSSeq h = rewrite plusSuccLeftSucc ((plus (plus h (S h)) (S h))) (S h) in Refl

export
plusthreeSeq : (h:Nat) ->  (3 + plus (S h) (plus (plus (S h) (S h)) (S h))) = (3 + (S (plus (plus (plus h (S h)) (S h)) (S h))))
plusthreeSeq h = rewrite plusSSeq h in rewrite plusCommutative (plus (plus (S h) (S h)) (S h)) (S h) in Refl

export
%hint
plus4i : {i:Nat} ->  plus i (((i + i) + i) + S i) = plus (plus (plus (plus i i) i) i) (S i)
plus4i =  rewrite plusAssociative' i (plus (plus i i) i) (S i) in rewrite plusCommutative i (plus (plus i i) i) in Refl


--left + (centre + right) = (left + centre) + right

--(S (S (S (S (plus h (S (plus (plus h (S h)) (S h))))))))
--Small helper lemmas to make the actual functions look less messy--
ltz1: LT 0 1
ltz1 = lteRefl 1

ltzs: (k:Nat) -> LT Z (S k) 
ltzs 0 = lteRefl 1  
ltzs (S k) = lteSuccRight $ ltzs k

ltzss: (k:Nat) -> LT Z (S (S k)) 
ltzss 0 = LTESucc LTEZero 
ltzss (S k) = lteSuccRight $ ltzss k

lt1ss: (k:Nat) -> LT 1 (S (S k))
lt1ss Z = lteRefl 2
lt1ss (S k) = lteSuccRight $ lt1ss k

--------------------------------------------------------------------


--LEMMAS ABOUT <, >, =, /=, <=, >= : TRANSITIVITY

||| Do not turn into a hint, it will make compilation far too long
export 
lemmaTransLTESLTE : (i : Nat) -> (n : Nat) -> (p : Nat) -> LTE i n -> LTE (S n) p -> LTE (S i) p
lemmaTransLTESLTE 0 0 (S k) _ _ = lemma1LTESucc k
lemmaTransLTESLTE i n k prf1 prf2 = lteTransitive (LTESucc prf1) prf2
--lemmaTransLTESLTE (S k) (S n) (S p) prf1 prf2 =  lteTransitive (LTESucc prf1) prf2 --LTESucc $ lemmaTransLTESLTE k n p (fromLteSucc prf1) (fromLteSucc prf2)

export
lemmaTransLTELT : (i : Nat) -> (n : Nat) -> (p : Nat) -> LTE i n -> LT n p -> LT i p
lemmaTransLTELT = lemmaTransLTESLTE

export
lemmaTransLTLTE : (i : Nat) -> (n : Nat) -> (p : Nat) -> LT i n -> LTE n p -> LT i p
lemmaTransLTLTE i n k prf1 prf2 = lteTransitive prf1 prf2

export
lemmaTransitivity : (i : Nat) -> (n : Nat) -> (p : Nat) -> LT i n -> LT n p -> LT i p
lemmaTransitivity i n k prf1 prf2 = lteTransitive prf1 (lteSuccLeft prf2)


--LEMMAS USED BY THE APPLY FUNCTION (with Either)
export
indexInjectiveVect : (j : Nat) -> (n : Nat) -> (v : Vect i Nat) ->
                     {auto prf : IsInjectiveT n v} -> {prf1 : LT j i} ->
                     LT (indexLT j v) n
indexInjectiveVect Z n (x :: xs) {prf} = getPrfSmaller $ getAllSmaller prf
indexInjectiveVect (S k) n (x :: xs) {prf} = indexInjectiveVect k n xs {prf = ifInjectiveThenSubInjective prf}
 

export
different' : (x : Nat) -> (m : Nat) -> (xs : Vect i Nat) ->
             {prf1 : LT m i} -> {prf2 : IsDifferentT x xs} ->
             Either (LT x (indexLT m xs)) (LT (indexLT m xs) x)
different' x 0 (y :: xs) = isDiffToPrf prf2
different' x (S k) (y :: xs) = different' x k xs {prf1 = fromLteSucc prf1} {prf2 = ifDiffThenSubDiff prf2}

private
different'' : (x : Nat) -> (m : Nat) -> (xs : Vect i Nat) ->
             {prf1 : LT m i} -> {prf2 : IsDifferentT x xs} ->
              Either (LT (indexLT m xs) x) (LT x (indexLT m xs)) 
different'' x 0 (y :: xs) =  mirror $ isDiffToPrf prf2
different'' x (S k) (y :: xs) = different'' x k xs {prf1 = fromLteSucc prf1} {prf2 = ifDiffThenSubDiff prf2}
             

export
differentIndexInjectiveVect : (c : Nat) -> (t : Nat) -> (n : Nat) -> {prf1 :  Either (LT c t) (LT t c)} ->
                              (v : Vect i Nat) -> {prf2 : IsInjectiveT n v} ->
                              {prf3 : LT c i } -> {prf4 : LT t i } ->
                              Either (LT (indexLT c v) (indexLT t v)) (LT (indexLT t v) (indexLT c v))
differentIndexInjectiveVect 0 0 _ _ = absurd prf1
differentIndexInjectiveVect 0 (S m) n (x :: xs) =
      different' x m xs {prf1 = fromLteSucc prf4} {prf2 = allDiffToPrf $ getAllDifferent prf2}
differentIndexInjectiveVect (S k) 0 n (x :: xs) =
      different'' x k xs {prf1 = fromLteSucc prf3} {prf2 = allDiffToPrf $ getAllDifferent prf2}
differentIndexInjectiveVect (S k) (S j) n (x :: xs) =
  differentIndexInjectiveVect k j n {prf1 = eitherLTSucc prf1} xs {prf2 = ifInjectiveThenSubInjective prf2} {prf3 = fromLteSucc prf3} {prf4 = fromLteSucc prf4}

--LEMMAS USED BY THE APPLY FUNCTION (with void)

export
indexInjectiveVectDec : (j : Nat) -> (n : Nat) -> (v : Vect i Nat) ->
                     {auto prf : IsInjectiveDec n v} -> {prf1 : LT j i} ->
                     LT (indexLT j v) n
indexInjectiveVectDec Z n (x :: xs) {prf} = getPrfSmaller $ getAllSmallerDec prf
indexInjectiveVectDec (S k) n (x :: xs) {prf} = indexInjectiveVectDec k n xs {prf = ifInjectiveDecThenSubInjectiveDec prf}  

export
%hint
implementation Uninhabited (Z = Z -> Void) where
  uninhabited f = f Refl

export
differentDec' : (x : Nat) -> (m : Nat) -> (xs : Vect i Nat) ->
             {prf1 : LT m i} -> {prf2 : IsDifferentDec x xs} ->
              (x = (indexLT m xs) -> Void)
differentDec' x 0 (y :: xs) = isDiffToPrfDec prf2
differentDec' x (S k) (y :: xs) = differentDec' x k xs {prf1 = fromLteSucc prf1} {prf2 = ifDiffThenSubDiffDec prf2}

private
differentDec'' : (x : Nat) -> (m : Nat) -> (xs : Vect i Nat) ->
             {prf1 : LT m i} -> {prf2 : IsDifferentDec x xs} ->
             ( (indexLT m xs) = x -> Void) 
differentDec'' x 0 (y :: xs) =  eqSymVoid (isDiffToPrfDec (prf2))
differentDec'' x (S k) (y :: xs) = differentDec'' x k xs {prf1 = fromLteSucc prf1} {prf2 = ifDiffThenSubDiffDec prf2}  

export
differentIndexInjectiveVectDec : {i : Nat} -> (c : Nat) -> (t : Nat) -> (n : Nat) -> {prf1 : c = t -> Void } ->
                              (v : Vect i Nat) -> {prf2 : IsInjectiveDec n v} ->
                              {prf3 : LT c i } -> {prf4 : LT t i } ->
                              ((indexLT c v)  = (indexLT t v) -> Void)
differentIndexInjectiveVectDec 0 0 _ _ = absurd prf1
differentIndexInjectiveVectDec 0 (S m) n (x :: xs) =
      differentDec' x m xs {prf1 = fromLteSucc prf4} {prf2 = allDiffDecToPrf$ getAllDifferentDec prf2}
differentIndexInjectiveVectDec (S k) 0 n (x :: xs) =
      differentDec'' x k xs {prf1 = fromLteSucc prf3} {prf2 = allDiffDecToPrf $ getAllDifferentDec prf2}
differentIndexInjectiveVectDec (S k) (S j) n (x :: xs) =
  differentIndexInjectiveVectDec k j n {prf1 = eqVoidSucc prf1} xs {prf2 = ifInjectiveDecThenSubInjectiveDec prf2} {prf3 = fromLteSucc prf3} {prf4 = fromLteSucc prf4}

--------------------------------------------------------------------
--------------LEMMAS USED BY THE CONTROLLED FUNCTION ---------------
--------------------------------------------------------------------


export
lemmaControlledInj : (n : Nat) -> (j : Nat) -> {auto prf : LT j n} -> IsInjectiveT (S n) [0, S j]
lemmaControlledInj 0 0 impossible
lemmaControlledInj 0 (S k) {prf} = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltzss k)) (IsDiffNil)) (AllDiffSucc (IsDiffNil) (AllDiffNil)))
  (ASSucc (ltz1) (ASSucc (LTESucc prf) (ASNil)))
lemmaControlledInj (S k) 0 = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltz1)) (IsDiffNil)) (AllDiffSucc (IsDiffNil) (AllDiffNil)))
  (ASSucc (ltzss k) (ASSucc (LTESucc prf) (ASNil)))
lemmaControlledInj (S p) (S k) {prf} = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltzss k)) (IsDiffNil)) (AllDiffSucc (IsDiffNil) (AllDiffNil)))
  (ASSucc (ltzss p) (ASSucc (LTESucc prf) (ASNil)))

export
lemmaControlledInj2 : (n : Nat) -> (c : Nat) -> (t : Nat) ->
                      {auto prf1 : LT c n} -> {auto prf2 : LT t n} -> {auto prf3 : Either (LT c t) (LT t c)} ->
                      IsInjectiveT (S n) [0, S c, S t]
lemmaControlledInj2 0 0 t impossible
lemmaControlledInj2 0 (S k) t {prf1} {prf2} {prf3}= IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltzss k)) (IsDiffSucc (Left (ltzs t)) (IsDiffNil))) 
    (AllDiffSucc (IsDiffSucc (eitherLTtoSucc prf3) (IsDiffNil)) 
      (AllDiffSucc (IsDiffNil) (AllDiffNil))))
  (ASSucc (ltz1) (ASSucc (LTESucc prf1) (ASSucc (LTESucc prf2) (ASNil))))

lemmaControlledInj2 (S k) 0 0 {prf3} = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltz1)) (IsDiffSucc (Left (ltz1)) (IsDiffNil))) 
    (AllDiffSucc (IsDiffSucc (eitherLTtoSucc prf3) (IsDiffNil)) 
      (AllDiffSucc (IsDiffNil) (AllDiffNil))))
  (ASSucc (ltzss k) (ASSucc (LTESucc prf1) (ASSucc (LTESucc prf2) (ASNil))))

lemmaControlledInj2 (S k) 0 (S j) = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltz1)) (IsDiffSucc (Left (ltzss j)) (IsDiffNil))) 
    (AllDiffSucc (IsDiffSucc (Left (lt1ss j)) (IsDiffNil)) 
      (AllDiffSucc (IsDiffNil) (AllDiffNil))))
  (ASSucc (ltzss k) (ASSucc (LTESucc prf1) (ASSucc (LTESucc prf2) (ASNil))))

lemmaControlledInj2 (S k) (S j) 0 = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltzss j)) (IsDiffSucc (Left (ltz1)) (IsDiffNil))) 
    (AllDiffSucc (IsDiffSucc (Right (lt1ss j)) (IsDiffNil)) 
      (AllDiffSucc (IsDiffNil) (AllDiffNil))))
  (ASSucc (ltzss k) (ASSucc (LTESucc prf1) (ASSucc (LTESucc prf2) (ASNil))))

lemmaControlledInj2 (S k) (S j) (S i) = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Left (ltzss j)) (IsDiffSucc (Left (ltzss i)) (IsDiffNil))) 
    (AllDiffSucc (IsDiffSucc (eitherLTtoSucc prf3) (IsDiffNil)) 
      (AllDiffSucc (IsDiffNil) (AllDiffNil))))
  (ASSucc (ltzss k) (ASSucc (LTESucc prf1) (ASSucc (LTESucc prf2) (ASNil))))
                    


{-
export

lemmaSuccInjg: {k:Nat} -> IsInjectiveT (S (S k)) [S k, 0]
lemmaSuccInjg {k} = findProofIsInjectiveTk {m = \l => S (S k)} {v = \d => [ S d, 0]}

export

lemmaSuccInj: {k:Nat} -> IsInjectiveT (S (S k)) [S k, 0]
lemmaSuccInj {k} = IsInjectiveSucc 
  (AllDiffSucc (IsDiffSucc (Right (ltzs k)) (IsDiffNil)) (AllDiffSucc (IsDiffNil) (AllDiffNil)))
(ASSucc (lteRefl (S (S k))) (ASSucc (ltzss k) (ASNil))) 


export

lemmaSuccInjPlus: {k:Nat} -> IsInjectiveT (S (k + 1)) [S k, 0]  
lemmaSuccInjPlus {k} = rewrite sym $ Data.Nat.plusOneSucc k in (rewrite plusCommutative k 1 in lemmaSuccInjg)-}

--LEMMAS USED BY THE TENSOR FUNCTION (with Either)
export
lemmaDiffSuccPlusE : (k : Nat) -> (p : Nat) -> Either (LT k (S (p + k))) (LT (S (p + k)) k)
lemmaDiffSuccPlusE 0 p = rewrite plusZeroRightNeutral p in Left (ltzs p)
lemmaDiffSuccPlusE (S k) j = (rewrite sym $ plusSuccRightSucc j k in (eitherLTtoSucc (lemmaDiffSuccPlusE k j)))

export
isDiffRangeVect : (k : Nat) -> (length : Nat) -> (p : Nat) -> IsDifferentT k (rangeVect (S (p + k)) length)
isDiffRangeVect k 0 _ = IsDiffNil
isDiffRangeVect k (S j) p = IsDiffSucc (lemmaDiffSuccPlusE k p) (isDiffRangeVect k j (S p))

export
allDiffRangeVect : (startIndex : Nat) -> (length : Nat) -> AllDifferentT (rangeVect startIndex length)
allDiffRangeVect startIndex 0 = AllDiffNil
allDiffRangeVect startIndex (S k) = 
  let p1 = isDiffRangeVect startIndex k 0
  in AllDiffSucc p1 (allDiffRangeVect (S startIndex) k)

export
allSmallerRangeVect : (startIndex : Nat) -> (length : Nat) -> AllSmallerT (rangeVect startIndex length) (startIndex + length)
allSmallerRangeVect startIndex 0 = ASNil
allSmallerRangeVect startIndex (S k) = 
  rewrite sym $ plusSuccRightSucc startIndex k in 
          ASSucc (lemmaLTSuccPlus startIndex k) (allSmallerRangeVect (S startIndex) k) 

export
allSmallerPlus : (n : Nat) -> (p : Nat) -> (v : Vect k Nat) -> AllSmallerT v n -> AllSmallerT v (n + p)
allSmallerPlus n p [] prf = ASNil
allSmallerPlus n p v prf = ifAllSmallThenPlusSmall p prf 

export 
isInjectiveRangeVect : (startIndex : Nat) -> (length : Nat) -> IsInjectiveT (startIndex+length) (rangeVect startIndex length)
isInjectiveRangeVect i length = IsInjectiveSucc (allDiffRangeVect i length) (allSmallerRangeVect i length)

--LEMMAS USED BY THE TENSOR FUNCTION (with Void)

-- derive contra from k = S (j + k) 
impossibleEq : (j, k : Nat) -> k = S (j + k) -> Void
impossibleEq j  Z     Refl impossible                              -- 0 ≠ S _
impossibleEq j (S k') eq =
  let
    p1= rewrite plusSuccRightSucc j k' in eq
    p2 = succInjective p1
  in
    impossibleEq j k' p2

||| Giving the implementation outside did not seem to work, so I pulled it inside
export
lemmaDiffSuccPlusEDec : (k : Nat) -> (p : Nat) -> (k  = (S (p + k)) -> Void)
lemmaDiffSuccPlusEDec 0 p eq = absurd eq
lemmaDiffSuccPlusEDec (S k) j eq = let 
      implementation Uninhabited ((S k = S (j + S k))) where
          uninhabited eqn = impossibleEq j k (succInjective (rewrite plusSuccRightSucc j k in eqn))
      in
        absurd (uninhabited (eq))
 
export
isDiffRangeVectDec : (k : Nat) -> (length : Nat) -> (p : Nat) -> IsDifferentDec k (rangeVect (S (p + k)) length)
isDiffRangeVectDec k 0 _ = IsDiffNilDec
isDiffRangeVectDec k (S j) p = IsDiffSuccDec (lemmaDiffSuccPlusEDec k p) (isDiffRangeVectDec k j (S p))

export
allDiffRangeVectDec : (startIndex : Nat) -> (length : Nat) -> AllDifferentDec (rangeVect startIndex length)
allDiffRangeVectDec startIndex 0 = AllDiffNilDec
allDiffRangeVectDec startIndex (S k) = 
  let p1 = isDiffRangeVectDec startIndex k 0
  in AllDiffSuccDec p1 (allDiffRangeVectDec (S startIndex) k)

export
allSmallerRangeVectDec : (startIndex : Nat) -> (length : Nat) -> AllSmallerT (rangeVect startIndex length) (startIndex + length)
allSmallerRangeVectDec startIndex 0 = ASNil
allSmallerRangeVectDec startIndex (S k) = 
  rewrite sym $ plusSuccRightSucc startIndex k in 
    ASSucc (lemmaLTSuccPlus startIndex k) (allSmallerRangeVectDec (S startIndex) k) 

export 
isInjectiveRangeVectDec : (startIndex : Nat) -> (length : Nat) -> IsInjectiveDec (startIndex+length) (rangeVect startIndex length)
isInjectiveRangeVectDec i length = IsInjectiveSuccDec (allDiffRangeVectDec i length) (allSmallerRangeVectDec i length)


{-}
-- Safe indexing by Nat (returns Nothing if out of bounds)
getAt : {n : Nat} -> Nat -> Vect n Nat -> Maybe Nat
getAt {n} i xs = case isLT i n of 
  Yes prf => Just (indexLT i xs) 
  No _ => Nothing

-- Half for Nat
half : Nat -> Nat
half Z = Z
half k = div k 2

-- Core routine: search between [start .. end] (inclusive)
findFirstMissing : {n : Nat} -> Vect n Nat -> (start: Nat) -> (end: Nat) -> Nat
findFirstMissing arr start end =
  if start > end then end + 1
  else case getAt start arr of
    -- if a[start] != start, we found the first gap
    Just v =>
      if v /= start then start
      else
        let mid = half (start + end) in
        case getAt mid arr of
          Just vm =>
            if vm == mid
              then findFirstMissing arr (mid + 1) end
              else findFirstMissing arr start mid
          -- mid out of bounds: conservatively say "end + 1"
          Nothing => end + 1
    -- start out of bounds: conservatively say "end + 1"
    Nothing => end + 1

-- Convenience wrapper: search the whole vector range [0 .. n-1]
findFirstMissingFull : {n : Nat} -> Vect n Nat -> Nat
findFirstMissingFull {n} arr =
  case n of
    Z   => 0
    S k => findFirstMissing arr 0 k

export

findProofIsDiffOrFailDec : (m:Nat) -> (v: Vect n Nat) -> IsDifferentDec m v
findProofIsDiffOrFailDec m [] = IsDiffNilDec
findProofIsDiffOrFailDec m (x::xs) = case decEq m x of
  No prfNo => IsDiffSuccDec (prfNo ) (findProofIsDiffOrFailDec m xs)
  Yes prfLeft => assert_total $ idris_crash "There exists no automatic proof that the Vector is Injective"

export 
    
findProofAllDiffOrFailDec : {v: Vect n Nat} -> AllDifferentDec v
findProofAllDiffOrFailDec {v = []} = AllDiffNilDec
findProofAllDiffOrFailDec {v = (x::xs)} = AllDiffSuccDec (findProofIsDiffOrFailDec x xs) (findProofAllDiffOrFailDec {v = xs})

export 
 
findProofAllSmallerOrFailDec : (m:Nat) -> (v: Vect n Nat) -> AllSmallerT v m
findProofAllSmallerOrFailDec {m} {v = []} = ASNil
findProofAllSmallerOrFailDec {m} {v = (x::xs)} = case isLT x m of
  No prfNo1 =>assert_total $ idris_crash "There exists no automatic proof that the Vector is Injective"
  Yes prfLT => ASSucc prfLT (findProofAllSmallerOrFailDec {m = m} {v = xs})

export 
 
lemmaIsInjectiveDec : {m:Nat} -> {v: Vect n Nat} -> IsInjectiveDec m v
lemmaIsInjectiveDec {m} {v} = IsInjectiveSuccDec (findProofAllDiffOrFailDec {v = v}) (findProofAllSmallerOrFailDec {m = m} {v = v})

export 
 
lemmaIsInjectiveDecT : {m: Nat -> Nat} -> {v: Nat-> Vect n Nat} -> ({k: Nat} -> IsInjectiveDec (m k) (v k))
lemmaIsInjectiveDecT {m} {v} = IsInjectiveSuccDec (findProofAllDiffOrFailDec {v = v k}) (findProofAllSmallerOrFailDec {m = m k} {v = v k})

export

implementation {j,k :Nat} -> Uninhabited ((S k = S (j + S k))) where
        uninhabited eqn = impossibleEq j k (succInjective (rewrite plusSuccRightSucc j k in eqn))

export

implementation Uninhabited (S k = k) where
        uninhabited Refl impossible

export

implementation Uninhabited (k = S k) where
        uninhabited Refl impossible
                
export

voidGenLeft : {k : Nat} -> S k = k -> Void
voidGenLeft eq = absurd eq


export

voidGenRight : {k : Nat} -> k = S k -> Void
voidGenRight eq = absurd eq
-}