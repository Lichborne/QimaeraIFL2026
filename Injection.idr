module Injection

import Data.Vect
import Data.Nat
import LinearTypes
import Decidable.Equality

%default total
-----------------------Syntactic tests for either----------------------------

||| True if the argument is Left, False otherwise
export
isLeft : Either a b -> Bool
isLeft (Left l)  = True
isLeft (Right r) = False
    
||| True if the argument is Right, False otherwise
export
isRight : Either a b -> Bool
isRight (Left l)  = False
isRight (Right r) = True

----LTE transitivity restated from library ----------------------------------
export 
||| `LTE` is transitive frommain library, unimported
lteTransitive : LTE n m -> LTE m p -> LTE n p
lteTransitive LTEZero y = LTEZero
lteTransitive (LTESucc x) (LTESucc y) = LTESucc (lteTransitive x y)
-----------------------------------------------------------------------------

|||Is a Nat different from all the Nats in a vector?
public export
isDifferent : Nat -> Vect n Nat -> Bool
isDifferent n [] = True
isDifferent n (x :: xs) = (n /= x) && isDifferent n xs

|||Are all the elements of a Nat vector different?
public export
allDifferent : Vect n Nat -> Bool
allDifferent [] = True
allDifferent (x :: xs) = isDifferent x xs && allDifferent xs

|||Are all the elements in a vector smaller than a given Nat?
public export 
allSmaller : Vect n Nat -> Nat -> Bool
allSmaller [] m = True
allSmaller (x :: xs) m = (x < m) && allSmaller xs m


public export
isInjective : Nat -> Vect n Nat -> Bool
isInjective m v = allSmaller v m && allDifferent v

|||Returns the element at index k in a vector
public export
index : (k : Nat) -> Vect n Nat -> {auto prf : (k < n) = True} -> Nat
index Z     (x::_)  = x
index (S k) (_::xs) = index k xs

public export
indexLT : (k : Nat) -> Vect n Nat -> {auto prf : LT k n} -> Nat
indexLT Z     (x::_) {prf} = x
indexLT (S k) (_::xs) {prf} = indexLT k xs {prf = fromLteSucc prf}

public export
indexLTL : (k : Nat) -> (1_: Vect n Nat) -> {auto prf : LT k n} -> LFstPair (Vect n Nat) Nat
indexLTL Z (x::xs) {prf} = (x::xs) # x
indexLTL (S k) (x::xs) {prf} = let (qs # m) = indexLTL k xs {prf = fromLteSucc prf} in (x :: qs) # m


|||Returns the vector [1,2,...,n]
public export
rangeVect : (startIndex : Nat) -> (length : Nat) -> Vect length Nat
rangeVect k Z = []
rangeVect k (S i) = k :: rangeVect (S k) i

------------------------------------------------------------------------------
---------------------------------------------------------------------------
public export
data AllSmallerT : (v: Vect n Nat) -> (m:Nat) -> Type where
    ASNil  : AllSmallerT [] m 
    ASSucc :  LT x m -> (soFarSmaller: AllSmallerT xs m)-> AllSmallerT (x :: xs) m

export
getPrfSmaller : AllSmallerT v m -> LT (head v) m
getPrfSmaller ASNil impossible
getPrfSmaller (ASSucc prf sfs) = prf

|||Are all the elements in a vector smaller than a given Nat?
public export 
allSmallerT : Vect n Nat -> Nat -> Type
allSmallerT v m = AllSmallerT v m 

export
ifAllSmallThenSubSmall : AllSmallerT (x::xs) m -> AllSmallerT xs m
ifAllSmallThenSubSmall (ASSucc a b) = b

export
plusLT : {a,b:Nat} -> (c:Nat) -> LT a b -> LT a (b+c)
plusLT Z prf = rewrite plusZeroRightNeutral b in prf 
plusLT {a} {b} (S c) prf = lteTransitive prf (lteAddRight b)

export
ifAllSmallThenPlusSmall : {v: Vect k Nat} -> {m: Nat} -> (n:Nat) -> AllSmallerT v m -> AllSmallerT v (m+n) 
ifAllSmallThenPlusSmall any ASNil = ASNil
ifAllSmallThenPlusSmall Z prf = rewrite plusZeroRightNeutral m in prf 
ifAllSmallThenPlusSmall {v = (x::xs)} {m} (S n) (ASSucc (lt) prev) =  ASSucc (plusLT {a = x} {b = m} (S n) lt) (ifAllSmallThenPlusSmall (S n) prev)

public export
data IsDifferentT : (m: Nat) -> (v: Vect n Nat) -> Type where
    IsDiffNil  : IsDifferentT m []
    IsDiffSucc : (Either (LT m x) (LT x m)) -> (soFarDiff: IsDifferentT m xs) -> IsDifferentT m (x :: xs)

export
isDifferentT : Nat -> Vect n Nat -> Type
isDifferentT n v = IsDifferentT n v

export
ifDiffThenSubDiff : IsDifferentT m (x::xs) -> IsDifferentT m xs
ifDiffThenSubDiff (IsDiffSucc a b) = b

export
isDiffToPrf : IsDifferentT m (x::xs) -> Either (LT m x) (LT x m)
isDiffToPrf (IsDiffSucc a b) = a

public export
data AllDifferentT : (v: Vect n Nat) -> Type where
    AllDiffNil  : AllDifferentT []
    AllDiffSucc : IsDifferentT x xs -> (soFarDiff: AllDifferentT xs)-> AllDifferentT (x :: xs)

export
ifAllDiffThenSubDiff : AllDifferentT (x::xs) -> AllDifferentT xs
ifAllDiffThenSubDiff (AllDiffSucc a b) = b

export
allDiffToPrf: AllDifferentT (x::xs) -> IsDifferentT x xs
allDiffToPrf (AllDiffSucc a b) = a

public export
allDifferentT : Vect n Nat -> Type
allDifferentT v = AllDifferentT v

public export
data IsInjectiveT : (m:Nat) -> (v: Vect n Nat) -> Type where
    IsInjectiveSucc : AllDifferentT v -> AllSmallerT v m-> IsInjectiveT m v

public export
isInjectiveT : Nat -> Vect n Nat -> Type
isInjectiveT m v = IsInjectiveT m v

export
getAllSmaller: IsInjectiveT m v -> AllSmallerT v m
getAllSmaller (IsInjectiveSucc prf1 prf2) = prf2

export
getAllDifferent : IsInjectiveT m v -> AllDifferentT v
getAllDifferent (IsInjectiveSucc prf1 prf2) = prf1

export
ifInjectiveThenSubInjective : IsInjectiveT m (x::xs) -> IsInjectiveT m xs
ifInjectiveThenSubInjective (IsInjectiveSucc allDiff allSmall)= IsInjectiveSucc (ifAllDiffThenSubDiff allDiff) (ifAllSmallThenSubSmall allSmall)

||| Alternative - equality to Void

public export
data IsDifferentDec : (m: Nat) -> (v: Vect n Nat) -> Type where
    IsDiffNilDec  : IsDifferentDec m []
    IsDiffSuccDec : (m = x -> Void)-> (soFarDiff: IsDifferentDec m xs)-> IsDifferentDec m (x :: xs)

export
isDifferentDec : Nat -> Vect n Nat -> Type
isDifferentDec n v = IsDifferentDec n v

export
ifDiffThenSubDiffDec  : IsDifferentDec  m (x::xs) -> IsDifferentDec m xs
ifDiffThenSubDiffDec (IsDiffSuccDec a b) = b

export
isDiffToPrfDec : IsDifferentDec k (x::xs) -> (k = x -> Void)
isDiffToPrfDec (IsDiffSuccDec a b) = a

export
eqSymVoid : (k = x -> Void) -> (x = k -> Void)
eqSymVoid kxToVoid Refl = kxToVoid Refl


public export
data AllDifferentDec : (v: Vect n Nat) -> Type where
    AllDiffNilDec  : AllDifferentDec []
    AllDiffSuccDec : IsDifferentDec x xs -> (soFarDiff: AllDifferentDec xs)-> AllDifferentDec (x :: xs)

export
ifAllDiffDecThenSubDiffDec : AllDifferentDec (x::xs) -> AllDifferentDec xs
ifAllDiffDecThenSubDiffDec (AllDiffSuccDec a b) = b

export
allDiffDecToPrf : AllDifferentDec (x::xs) -> IsDifferentDec x xs
allDiffDecToPrf (AllDiffSuccDec a b) = a

public export
allDifferentDec : Vect n Nat -> Type
allDifferentDec v = AllDifferentDec v

public export
data IsInjectiveDec : (m:Nat) -> (v: Vect n Nat) -> Type where
    IsInjectiveSuccDec : AllDifferentDec v -> AllSmallerT v m -> IsInjectiveDec m v

public export
isInjectiveDec : Nat -> Vect n Nat -> Type
isInjectiveDec m v = IsInjectiveDec m v

export
getAllSmallerDec : IsInjectiveDec m v -> AllSmallerT v m
getAllSmallerDec (IsInjectiveSuccDec prf1 prf2) = prf2

export
getAllDifferentDec : IsInjectiveDec m v -> AllDifferentDec v
getAllDifferentDec (IsInjectiveSuccDec prf1 prf2) = prf1

export
ifInjectiveDecThenSubInjectiveDec : IsInjectiveDec m (x::xs) -> IsInjectiveDec m xs
ifInjectiveDecThenSubInjectiveDec (IsInjectiveSuccDec allDiff allSmall) =
    IsInjectiveSuccDec (ifAllDiffDecThenSubDiffDec allDiff) (ifAllSmallThenSubSmall allSmall)   


export 
findProofIsDiffOrNothing : (m:Nat) -> (v: Vect n Nat) -> Maybe (IsDifferentT m v)
findProofIsDiffOrNothing m [] = Just IsDiffNil
findProofIsDiffOrNothing m (x::xs) = case isLT m x of
   Yes prfLeft => case (findProofIsDiffOrNothing m xs) of 
    Just isdif => Just $ IsDiffSucc (Left prfLeft) isdif
    Nothing => Nothing
   No prfNo1 => case isLT x m of
     Yes prfRight => case (findProofIsDiffOrNothing m xs) of 
        Just isdif => Just $ IsDiffSucc (Right prfRight) isdif
        Nothing => Nothing
     No prfNo2 => Nothing
     _ => Nothing
   _ => Nothing

isDifSProp : (IsDifferentT m xs -> Void) -> (IsDifferentT m (x :: xs)) -> Void
isDifSProp IsDiffNil void IsDiffNil impossible
isDifSProp (IsDiffSucc either prev) void IsDiffNil impossible
isDifSProp (IsDiffSucc either prev) v (IsDiffSucc eitherx IsDiffNil) impossible
isDifSProp f (IsDiffSucc eitherx prevx) = f prevx

eitherVoid: (left -> Void) -> (right-> Void) -> Either left right -> Void
eitherVoid fleft fright (Left l) = fleft l
eitherVoid fleft fright (Right r) = fright r

eitherVoidThenNotDif : (Either (LTE (S m) x) (LTE (S x) m) -> Void) -> IsDifferentT m (x :: xs) -> Void
eitherVoidThenNotDif feither IsDiffNil impossible
eitherVoidThenNotDif feither (IsDiffSucc either prev) = feither either


export 
eitherIsDiffOrNot : (m:Nat) -> (v: Vect n Nat) -> Either (IsDifferentT m v) (IsDifferentT m v -> Void)
eitherIsDiffOrNot m [] = Left IsDiffNil
eitherIsDiffOrNot m (x::xs) = 
    case isLT m x of
        Yes prfLeft => case (eitherIsDiffOrNot m xs) of 
            Left isdif => Left $ IsDiffSucc (Left prfLeft) isdif
            Right notdif => Right (isDifSProp (notdif))
        No prfNo1 => case isLT x m of
            Yes prfRight => case (eitherIsDiffOrNot m xs) of 
                Left isdif => Left $ IsDiffSucc (Right prfRight) isdif
                Right notdif => Right (isDifSProp (notdif))
            No prfNo2 => Right (eitherVoidThenNotDif $ eitherVoid prfNo1 prfNo2)
  

export 
findProofAllDiffOrNothing : {v: Vect n Nat} -> Maybe (AllDifferentT v)
findProofAllDiffOrNothing {v = []} = Just AllDiffNil
findProofAllDiffOrNothing {v = (x::xs)} = case (findProofIsDiffOrNothing x xs) of 
    Just isdif => case (findProofAllDiffOrNothing {v = xs}) of 
        Just alldif => Just $ AllDiffSucc isdif alldif
        Nothing => Nothing
    Nothing => Nothing

allDifSProp : (AllDifferentT xs -> Void) -> (AllDifferentT (x :: xs)) -> Void
allDifSProp AllDiffNil void AllDiffNil impossible
allDifSProp (AllDiffSucc either prev) void AllDiffNil impossible
allDifSProp (AllDiffSucc either prev) v (AllDiffSucc eitherx AllDiffNil) impossible
allDifSProp f (AllDiffSucc eitherx prevx) = f prevx

notAllDiffProp : (IsDifferentT x xs -> Void) -> AllDifferentT (x :: xs) -> Void
notAllDiffProp tovoid AllDiffNil impossible
notAllDiffProp tovoid (AllDiffSucc isdif prev) = tovoid isdif


export 
%hint
eitherAllDiffOrNot  : {v: Vect n Nat} -> Either (AllDifferentT v) (AllDifferentT v -> Void)
eitherAllDiffOrNot  {v = []} = Left AllDiffNil
eitherAllDiffOrNot {v = (x::xs)} = case (eitherIsDiffOrNot x xs) of 
    Left isdif => case (eitherAllDiffOrNot {v = xs}) of 
        Left alldif => Left (AllDiffSucc isdif alldif)
        Right notalldif => Right (allDifSProp notalldif)
    Right notalldif => Right (notAllDiffProp (notalldif))


export 
findProofAllSmallerOrNothing : (m:Nat) -> (v: Vect n Nat) -> Maybe (AllSmallerT v m)
findProofAllSmallerOrNothing {m} {v = []} = Just ASNil
findProofAllSmallerOrNothing {m} {v = (x::xs)} = case isLT x m of
  Yes prfLT => case (findProofAllSmallerOrNothing {m = m} {v = xs}) of 
    Just allsmaller => Just $ ASSucc prfLT allsmaller
    Nothing => Nothing
  No prfNo1 => Nothing

allSmallSProp : (AllSmallerT xs m -> Void) -> AllSmallerT (x :: xs) m -> Void
allSmallSProp ASNil void ASNil impossible
allSmallSProp (ASSucc lt prev) void ASNil impossible
allSmallSProp (ASSucc lt prev) v (ASSucc ltx ASNil) impossible
allSmallSProp f (ASSucc ltx prevx) = f prevx

notSmallerProp : (LTE (S x) m -> Void) -> AllSmallerT (x :: xs) m -> Void
notSmallerProp tovoid ASNil impossible
notSmallerProp tovoid (ASSucc lt prev) = tovoid lt

export 
%hint
eitherAllSmallerOrNot : (m:Nat) -> (v: Vect n Nat) -> Either (AllSmallerT v m) ((AllSmallerT v m) -> Void)
eitherAllSmallerOrNot  {m} {v = []} = Left ASNil
eitherAllSmallerOrNot  {m} {v = (x::xs)} = case isLT x m of
  Yes prfLT => case (eitherAllSmallerOrNot {m = m} {v = xs}) of 
    Left allsmaller => Left $ ASSucc prfLT allsmaller
    Right notallsmaller => Right $ allSmallSProp notallsmaller
  No notsmaller => Right $ notSmallerProp notsmaller


export  
findProofIsInjectiveTOrNothing : {m:Nat} -> {v: Vect n Nat} -> Maybe (IsInjectiveT m v)
findProofIsInjectiveTOrNothing {m} {v} = case (findProofAllDiffOrNothing {v = v}) of 
    Just alldif => case (findProofAllSmallerOrNothing {m = m} {v = v}) of 
        Just allsmaller => Just $ IsInjectiveSucc alldif allsmaller
        Nothing => Nothing
    Nothing => Nothing


notInjIfNotSmallProp : (AllSmallerT v m -> Void) -> IsInjectiveT m v -> Void
notInjIfNotSmallProp tovoid (IsInjectiveSucc alldif allsmaller) = tovoid allsmaller    

notInjIfNotDifProp : (AllDifferentT v -> Void) -> IsInjectiveT m v -> Void
notInjIfNotDifProp tovoid (IsInjectiveSucc alldif allsmaller) = tovoid alldif   


export 
%hint 
eitherIsInjectiveTOrNot : {m:Nat} -> {v: Vect n Nat} -> Either (IsInjectiveT m v) ((IsInjectiveT m v) -> Void)
eitherIsInjectiveTOrNot {m} {v} = case (eitherAllDiffOrNot {v = v}) of 
    Left alldif => case (eitherAllSmallerOrNot {m = m} {v = v}) of 
        Left allsmaller => Left $ IsInjectiveSucc alldif allsmaller
        Right notallsmaller => Right $ notInjIfNotSmallProp notallsmaller
    Right notalldiff => Right $ notInjIfNotDifProp notalldiff


export 
%hint
decInj : (m:Nat) -> (v : Vect n Nat) -> Dec (IsInjectiveT m v) 
decInj m v = case eitherIsInjectiveTOrNot {m = m} {v = v} of
    Left prfYes => Yes prfYes
    Right prfNo => No prfNo 

export   
%hint
decInjHint : {m:Nat} -> {v : Vect n Nat} -> Dec (IsInjectiveT m v) 
decInjHint {m} {v} = case eitherIsInjectiveTOrNot {m = m} {v = v} of
    Left prfYes => Yes prfYes
    Right prfNo => No prfNo 

{-

export 
%hint
findProofIsDiffOrFail : (m:Nat) -> (v: Vect n Nat) -> IsDifferentT m v
findProofIsDiffOrFail m [] = IsDiffNil
findProofIsDiffOrFail m (x::xs) = case isLT m x of
   Yes prfLeft => IsDiffSucc (Left prfLeft) (findProofIsDiffOrFail m xs)
   No prfNo1 => case isLT x m of
     Yes prfRight =>  IsDiffSucc (Right prfRight) (findProofIsDiffOrFail m xs)
     No prfNo2 => assert_total $ idris_crash ("There exists no automatic proof that the Vector " ++ show (x::xs) ++ " is Injective (not all different) " ++ show m ++ " is not different to " ++ show x)
     


export 
findProofAllDiffOrFail : {v: Vect n Nat} -> AllDifferentT v
findProofAllDiffOrFail {v = []} = AllDiffNil
findProofAllDiffOrFail {v = (x::xs)} = AllDiffSucc (findProofIsDiffOrFail x xs) (findProofAllDiffOrFail {v = xs})


export 
findProofAllSmallerOrFail : (m:Nat) -> (v: Vect n Nat) -> AllSmallerT v m
findProofAllSmallerOrFail {m} {v = []} = ASNil
findProofAllSmallerOrFail {m} {v = (x::xs)} = case isLT x m of
  Yes prfLT => ASSucc prfLT (findProofAllSmallerOrFail {m = m} {v = xs})
  No prfNo1 => assert_total $ idris_crash ("There exists no automatic proof that the Vector " ++ show (x::xs) ++ " is Injective (not all smaller): " ++ show x ++ " is not smaller than " ++ show m)
  
export 
findProofIsInjectiveTOrFail : {m:Nat} -> {v: Vect n Nat} -> IsInjectiveT m v
findProofIsInjectiveTOrFail {m} {v} = IsInjectiveSucc (findProofAllDiffOrFail {v = v}) (findProofAllSmallerOrFail {m = m} {v = v})

export  
findProofIsInjectiveTk : {m: Nat -> Nat} -> {v: Nat-> Vect n Nat} -> ({k: Nat} -> IsInjectiveT (m k) (v k))
findProofIsInjectiveTk {m} {v} = IsInjectiveSucc (findProofAllDiffOrFail {v = v k}) (findProofAllSmallerOrFail {m = m k} {v = v k})



{-public export
data EitherAnd : (sumType: Either a b) -> Type where
    EitherNil : EitherAnd sumType
    EitherCons : (e : sumType) -> (es: EitherAnd (Left e)) -> EitherAnd sum
-}

