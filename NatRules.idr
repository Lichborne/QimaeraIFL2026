module NatRules

import Data.Nat
import Data.So
import public Control.Relation
import public Control.Ord
import public Control.Order
import public Control.Function
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic


export
%hint
succNotLTEzero' : Not (LTE (S m) Z)
succNotLTEzero' LTEZero impossible

export
%hint
fromLteSucc' : LTE (S m) (S n) -> LTE m n
fromLteSucc' (LTESucc x) = x


lteRecallLeft' : LTE m n -> (m' : Nat ** m = m')
lteRecallLeft' LTEZero = (0 ** Refl)
lteRecallLeft' (LTESucc x) with (lteRecallLeft' x)
  lteRecallLeft' (LTESucc x) | (left ** Refl) = (S left ** Refl)

irrelevantLte' : {m : Nat} -> (0 prf : LTE m n) -> LTE m n
irrelevantLte' {m = 0} LTEZero = LTEZero
irrelevantLte' {m = (S k)} (LTESucc x) = LTESucc (irrelevantLte' x)

lteRecall' : LTE m n -> {p : Nat -> Nat} -> (0 prf : LTE (p m) q) -> LTE (p m) q
lteRecall' {m} x prf with (lteRecallLeft' x)
  lteRecall' {m = m} x prf | (m ** Refl) = irrelevantLte' prf

ltRecall' : LT m n -> {p : Nat -> Nat} -> (0 prf : LT (p m) q) -> LT (p m) q
ltRecall' {m} x prf with (lteRecallLeft' x)
  ltRecall' {m = m} x prf | (S m ** Refl) = irrelevantLte' prf

export
%hint
lteSuccRight' : LTE n m -> LTE n (S m)
lteSuccRight' LTEZero     = LTEZero
lteSuccRight' (LTESucc x) = LTESucc (lteSuccRight' x)

export
%hint
lteSuccLeft' : LTE (S n) m -> LTE n m 
lteSuccLeft' (LTESucc x) = lteSuccRight' x

export
%hint
lteAddRight' : (n : Nat) -> LTE n (n + m)
lteAddRight' Z = LTEZero
lteAddRight' (S k) {m} = LTESucc (lteAddRight {m} k)

export
%hint
notLTEImpliesGT' : {a, b : Nat} -> Not (a `LTE` b) -> a `GT` b
notLTEImpliesGT' {a = 0  }           not_z_lte_b    = absurd $ not_z_lte_b LTEZero
notLTEImpliesGT' {a = S a} {b = 0  } notLTE = LTESucc LTEZero
notLTEImpliesGT' {a = S a} {b = S k} notLTE = LTESucc (notLTEImpliesGT (notLTE . LTESucc))

export
%hint
LTEImpliesNotGT' : a `LTE` b -> Not (a `GT` b)
LTEImpliesNotGT' LTEZero q = absurd q
LTEImpliesNotGT' (LTESucc p) (LTESucc q) = LTEImpliesNotGT p q

export
%hint
notLTImpliesGTE' : {a, b : _} -> Not (LT a b) -> GTE a b
notLTImpliesGTE' notLT = fromLteSucc $ notLTEImpliesGT notLT

export
%hint
LTImpliesNotGTE' : a `LT` b -> Not (a `GTE` b)
LTImpliesNotGTE' p q = LTEImpliesNotGT q p

export
%hint
lteReflectsLTE' : (k : Nat) -> (n : Nat) -> lte k n === True -> k `LTE` n
lteReflectsLTE' (S k)  0    _ impossible
lteReflectsLTE' 0      0    _   = LTEZero
lteReflectsLTE' 0     (S k) _   = LTEZero
lteReflectsLTE' (S k) (S j) prf = LTESucc (lteReflectsLTE k j prf)

export
%hint
gteReflectsGTE' : (k : Nat) -> (n : Nat) -> gte k n === True -> k `GTE` n
gteReflectsGTE' k n prf = lteReflectsLTE n k prf

export
%hint
ltReflectsLT' : (k : Nat) -> (n : Nat) -> lt k n === True -> k `LT` n
ltReflectsLT' k n prf = lteReflectsLTE (S k) n prf

public export
%hint
ltOpReflectsLT' : (m,n : Nat) -> So (m < n) -> LT m n
ltOpReflectsLT' 0     (S k) prf = LTESucc LTEZero
ltOpReflectsLT' (S k) (S j) prf = LTESucc (ltOpReflectsLT k j prf)
ltOpReflectsLT' (S k) 0     prf impossible
ltOpReflectsLT' 0 0         prf impossible

export
%hint
gtReflectsGT' : (k : Nat) -> (n : Nat) -> gt k n === True -> k `GT` n
gtReflectsGT' k n prf = ltReflectsLT n k prf

export
%hint
plusZeroLeftNeutral' : (right : Nat) -> 0 + right = right
plusZeroLeftNeutral' _ = Refl

export
%hint
plusZeroRightNeutral' : (left : Nat) -> left + 0 = left
plusZeroRightNeutral' Z     = Refl
plusZeroRightNeutral' (S n) = Calc $
  |~ 1 + (n + 0)
  ~~ 1 + n ...(cong (1+) $ plusZeroRightNeutral' n)

export
%hint
plusSuccRightSucc' : (left, right : Nat) -> S (left + right) = left + (S right)
plusSuccRightSucc' Z _ = Refl
plusSuccRightSucc' (S left) right = Calc $
  |~ 1 + (1 + (left + right))
  ~~ 1 + (left + (1 + right)) ...(cong (1+) $ plusSuccRightSucc' left right)

export
%hint
plusCommutative' : (left, right : Nat) -> left + right = right + left
plusCommutative' Z right = Calc $
  |~ right
  ~~ right + 0 ..<(plusZeroRightNeutral right)
plusCommutative' (S left) right = Calc $
  |~ 1 + (left + right)
  ~~ 1 + (right + left) ...(cong (1+) $ plusCommutative' left right)
  ~~ right + (1 + left) ...(plusSuccRightSucc' right left)

export
%hint
plusAssociative' : (left, centre, right : Nat) ->
  left + (centre + right) = (left + centre) + right
plusAssociative' Z _ _ = Refl
plusAssociative' (S left) centre right = Calc $
  |~ 1 + (left + (centre + right))
  ~~ 1 + ((left + centre) + right) ...(cong (1+) $ plusAssociative' left centre right)

export
%hint
plusConstantRight' : (left, right, c : Nat) -> left = right ->
  left + c = right + c
plusConstantRight' _ _ _ Refl = Refl

export
%hint
plusConstantLeft' : (left, right, c : Nat) -> left = right ->
  c + left = c + right
plusConstantLeft' _ _ _ Refl = Refl

export
%hint
plusOneSucc' : (right : Nat) -> 1 + right = S right
plusOneSucc' _ = Refl


export 
ltToLTE : {left,right:Nat} -> LTE (S left) right = LT left right 
ltToLTE = Refl

export
%hint
plusLeftCancel' : (left, right, right' : Nat) ->
  left + right = left + right' -> right = right'
plusLeftCancel' Z _ _ p = p
plusLeftCancel' (S left) right right' p =
    plusLeftCancel' left right right' $ injective p

export
%hint
plusRightCancel' : (left, left', right : Nat) ->
  left + right = left' + right -> left = left'
plusRightCancel' left left' right p =
  plusLeftCancel' right left left' $ Calc $
  |~ right + left
  ~~ left  + right ...(plusCommutative right left)
  ~~ left' + right ...(p)
  ~~ right + left' ...(plusCommutative left' right)

export
%hint
plusLeftLeftRightZero' : (left, right : Nat) ->
  left + right = left -> right = Z
plusLeftLeftRightZero' left right p =
  plusLeftCancel left right Z $ Calc $
  |~ left + right
  ~~ left     ...(p)
  ~~ left + 0 ..<(plusZeroRightNeutral left)


zeroPlusLeftZero' : (a,b : Nat) -> (0 = a + b) -> a = 0
zeroPlusLeftZero' 0 0 Refl = Refl
zeroPlusLeftZero' (S k) b _ impossible

zeroPlusRightZero' : (a,b : Nat) -> (0 = a + b) -> b = 0
zeroPlusRightZero' 0 0 Refl = Refl
zeroPlusRightZero' (S k) b _ impossible

-- Proofs on *
{-
export
%hint
multZeroLeftZero : (right : Nat) -> Z * right = Z
multZeroLeftZero _ = Refl

export
%hint
multZeroRightZero : (left : Nat) -> left * Z = Z
multZeroRightZero Z        = Refl
multZeroRightZero (S left) = multZeroRightZero left

export
%hint
multRightSuccPlus : (left, right : Nat) ->
  left * (S right) = left + (left * right)
multRightSuccPlus Z _ = Refl
multRightSuccPlus (S left) right = cong (1+) $ Calc $
  |~ right + (left * (1 + right))
  ~~ right + (left + (left * right))
         ...(cong (right +) $ multRightSuccPlus left right)
  ~~ (right + left) + (left * right)
         ...(plusAssociative right left (left*right))
  ~~ (left + right) + (left * right)
         ...(cong (+ (left * right)) $ plusCommutative right left)
  ~~ left + (right + (left * right))
         ..<(plusAssociative left right (left * right))
  ~~ left + ((1 + left) * right)
         ...(Refl)

export
%hint
multLeftSuccPlus : (left, right : Nat) ->
  (S left) * right = right + (left * right)
multLeftSuccPlus _ _ = Refl

export
%hint
multCommutative : (left, right : Nat) -> left * right = right * left
multCommutative Z right = Calc $
  |~ 0
  ~~ right * 0 ..<(multZeroRightZero right)
multCommutative (S left) right = Calc $
  |~ right + (left * right)
  ~~ right + (right * left)
       ...(cong (right +) $ multCommutative left right)
  ~~ right * (1 + left)
       ..<(multRightSuccPlus right left)

export
%hint
multDistributesOverPlusLeft : (left, centre, right : Nat) ->
  (left + centre) * right = (left * right) + (centre * right)
multDistributesOverPlusLeft Z _ _ = Refl
multDistributesOverPlusLeft (S left) centre right = Calc $
  |~ right + ((left + centre) * right)
  ~~ right + ((left * right) + (centre * right))
        ...(cong (right +) $
            multDistributesOverPlusLeft left centre right)
  ~~ (right + (left * right)) + (centre * right)
        ...(plusAssociative right (left*right) (centre*right))
export
%hint
multDistributesOverPlusRight : (left, centre, right : Nat) ->
  left * (centre + right) = (left * centre) + (left * right)
multDistributesOverPlusRight left centre right = Calc $
  |~ left * (centre + right)
  ~~ (centre + right) * left ...(multCommutative left (centre + right))
  ~~ (centre * left) + (right * left)
                             ...(multDistributesOverPlusLeft centre right left)
  ~~ (left * centre) + (left * right)
                             ...(cong2 (+)
                                 (multCommutative centre left)
                                 (multCommutative right left))

export
%hint
multAssociative : (left, centre, right : Nat) ->
  left * (centre * right) = (left * centre) * right
multAssociative Z _ _ = Refl
multAssociative (S left) centre right = Calc $
  |~ (centre * right) + (left * (centre * right))
  ~~ (centre * right) + ((left * centre) * right)
        ...(cong ((centre * right) +) $
            multAssociative left centre right)
  ~~ ((1 + left) * centre) * right ..<(multDistributesOverPlusLeft centre (left * centre) right)

export
%hint
multOneLeftNeutral : (right : Nat) -> 1 * right = right
multOneLeftNeutral right = plusZeroRightNeutral right

export
%hint
multOneRightNeutral : (left : Nat) -> left * 1 = left
multOneRightNeutral left = Calc $
  |~ left * 1
  ~~ 1 * left ...(multCommutative left 1)
  ~~ left     ...(multOneLeftNeutral left)

-- Proofs on minus
-}
export
%hint
minusSuccSucc' : (left, right : Nat) ->
  minus (S left) (S right) = minus left right
minusSuccSucc' _ _ = Refl

export
%hint
minusZeroLeft' : (right : Nat) -> minus 0 right = Z
minusZeroLeft' _ = Refl

export
%hint
minusZeroRight' : (left : Nat) -> minus left 0 = left
minusZeroRight' Z     = Refl
minusZeroRight' (S _) = Refl

export
%hint
minusZeroN' : (n : Nat) -> Z = minus n n
minusZeroN' Z     = Refl
minusZeroN' (S n) = minusZeroN' n

export
%hint
minusOneSuccN' : (n : Nat) -> S Z = minus (S n) n
minusOneSuccN' Z     = Refl
minusOneSuccN' (S n) = minusOneSuccN' n

export
%hint
minusSuccOne' : (n : Nat) -> minus (S n) 1 = n
minusSuccOne' Z     = Refl
minusSuccOne' (S _) = Refl

export
%hint
minusPlusZero' : (n, m : Nat) -> minus n (n + m) = Z
minusPlusZero' Z     _ = Refl
minusPlusZero' (S n) m = minusPlusZero' n m

export
%hint
minusPos' : m `LT` n -> Z `LT` minus n m
minusPos' lt = case view lt of
  LTZero    => ltZero
  LTSucc lt => minusPos' lt

export
%hint
minusLteMonotone' : {p : Nat} -> m `LTE` n -> minus m p `LTE` minus n p
minusLteMonotone' LTEZero = LTEZero
minusLteMonotone' {p = Z} prf@(LTESucc _) = prf
minusLteMonotone' {p = S p} (LTESucc lte) = minusLteMonotone' lte

public export
%hint
minusPlus' : (m : Nat) -> minus (plus m n) m === n
minusPlus' Z = irrelevantEq (minusZeroRight' n)
minusPlus' (S m) = minusPlus' m

export
%hint
plusMinusLte' : (n, m : Nat) -> LTE n m -> (m `minus` n) + n = m
plusMinusLte'  Z     m    _   = Calc $
  |~ (m `minus` 0) + 0
  ~~ m + 0 ...(cong (+0) $ minusZeroRight m)
  ~~ m     ...(plusZeroRightNeutral m)
plusMinusLte' (S _)  Z    lte = absurd lte
plusMinusLte' (S n) (S m) lte = Calc $
  |~ ((1+m) `minus` (1+n)) + (1+n)
  ~~ (m `minus` n) + (1 + n) ...(Refl)
  ~~ 1+((m `minus` n) + n)   ..<(plusSuccRightSucc (m `minus` n) n)
  ~~ 1+m                     ...(cong (1+) $ plusMinusLte' n m
                                           $ fromLteSucc lte)

export
%hint
minusMinusMinusPlus' : (left, centre, right : Nat) ->
  minus (minus left centre) right = minus left (centre + right)
minusMinusMinusPlus' Z Z _ = Refl
minusMinusMinusPlus' (S _) Z _ = Refl
minusMinusMinusPlus' Z (S _) _ = Refl
minusMinusMinusPlus' (S left) (S centre) right = Calc $
  |~ (((1+left) `minus` (1+centre)) `minus` right)
  ~~ ((left `minus` centre) `minus` right) ...(Refl)
  ~~ (left `minus` (centre + right))       ...(minusMinusMinusPlus' left centre right)

export
%hint
plusMinusLeftCancel' : (left, right : Nat) -> (right' : Nat) ->
  minus (left + right) (left + right') = minus right right'
plusMinusLeftCancel' Z _ _ = Refl
plusMinusLeftCancel' (S left) right right' = Calc $
  |~ ((left + right) `minus` (left + right'))
  ~~ (right `minus` right') ...(plusMinusLeftCancel' left right right')

export
%hint
multDistributesOverMinusLeft' : (left, centre, right : Nat) ->
  (minus left centre) * right = minus (left * right) (centre * right)
multDistributesOverMinusLeft' Z Z _ = Refl
multDistributesOverMinusLeft' (S left) Z right = Calc $
  |~ right + (left * right)
  ~~ ((right + (left * right)) `minus` 0)
         ..<(minusZeroRight (right + (left*right)))
  ~~ (((1+left) * right) `minus` (0 * right))
         ...(Refl)
multDistributesOverMinusLeft' Z (S _) _ = Refl
multDistributesOverMinusLeft' (S left) (S centre) right = Calc $
  |~ ((1 + left) `minus` (1 + centre)) * right
  ~~ (left `minus` centre) * right
       ...(Refl)
  ~~ ((left*right) `minus` (centre*right))
       ...(multDistributesOverMinusLeft' left centre right)
  ~~ ((right + (left * right)) `minus` (right + (centre * right)))
      ..<(plusMinusLeftCancel right (left*right) (centre*right))
  ~~ (((1+ left) * right) `minus` ((1+centre) * right))
      ...(Refl)
export
%hint
multDistributesOverMinusRight' : (left, centre, right : Nat) ->
  left * (minus centre right) = minus (left * centre) (left * right)
multDistributesOverMinusRight' left centre right = Calc $
  |~ left * (centre `minus` right)
  ~~ (centre `minus` right) * left
         ...(multCommutative left (centre `minus` right))
  ~~ ((centre*left) `minus` (right*left))
         ...(multDistributesOverMinusLeft centre right left)
  ~~ ((left * centre) `minus` (left * right))
         ...(cong2 minus
             (multCommutative centre left)
             (multCommutative right left))
export
%hint
zeroMultEitherZero' : (a,b : Nat) -> a*b = 0 -> Either (a = 0) (b = 0)
zeroMultEitherZero' 0 b prf = Left Refl
zeroMultEitherZero' (S a) b prf = Right $ zeroPlusLeftZero' b (a * b) (sym prf)