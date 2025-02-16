module AccountSim where

open import Haskell.Prelude

PubKeyHash = Integer
Value = Integer

Datum = List (PubKeyHash × Value)

{-# COMPILE AGDA2HS Datum #-}

record ScriptContext : Set where
    field
        inputVal    : Integer
        outputVal   : Integer
        outputDatum : Datum 
        signature   : PubKeyHash
open ScriptContext public

data Input : Set where
  Open     : PubKeyHash -> Input
  Close    : PubKeyHash -> Input
  Withdraw : PubKeyHash -> Value -> Input
  Deposit  : PubKeyHash -> Value -> Input
  Transfer : PubKeyHash -> PubKeyHash -> Value -> Input

{-# COMPILE AGDA2HS Input #-}

insert : PubKeyHash -> Value -> Datum -> Datum
insert pkh val [] = ((pkh , val) ∷ [])
insert pkh val ((x , y) ∷ xs) = if (pkh == x)
  then ((pkh , val) ∷ xs)
  else ((x , y) ∷ (insert pkh val xs))
  
delete : PubKeyHash -> Datum -> Datum
delete pkh [] = []
delete pkh ((x , y) ∷ xs) = if (pkh == x)
  then xs
  else ((x , y) ∷ (delete pkh xs))

{-# COMPILE AGDA2HS insert #-}
{-# COMPILE AGDA2HS delete #-}

newDatum : ScriptContext -> Datum
newDatum ctx = outputDatum ctx

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = outputVal ctx

geq : Value -> Value -> Bool
geq val v = val >= v 

gt : Value -> Value -> Bool
gt val v = val > v

emptyValue : Value
emptyValue = 0

minValue : Value
minValue = 2

checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned pkh ctx = pkh == signature ctx

aux : Maybe Value -> Bool
aux Nothing = False
aux (Just _) = True

checkMembership' : PubKeyHash -> Datum -> Bool
checkMembership' pkh dat = case lookup pkh dat of λ where
  Nothing -> False
  (Just v) -> True

checkMembership : Maybe Value -> Bool
checkMembership Nothing = False
checkMembership (Just v) = True

checkEmpty : Maybe Value -> Bool
checkEmpty Nothing = False
checkEmpty (Just v) = v == emptyValue

checkWithdraw : Maybe Value -> PubKeyHash -> Value -> Datum -> ScriptContext -> Bool
checkWithdraw Nothing _ _ _ _ = False
checkWithdraw (Just v) pkh val dat ctx = geq val emptyValue && geq v val && (newDatum ctx == insert pkh (v - val) dat)

checkDeposit : Maybe Value -> PubKeyHash -> Value -> Datum -> ScriptContext -> Bool
checkDeposit Nothing _ _ _ _ = False
checkDeposit (Just v) pkh val dat ctx = geq val emptyValue && (newDatum ctx == insert pkh (v + val) dat)

checkTransfer : Maybe Value -> Maybe Value -> PubKeyHash -> PubKeyHash -> Value -> Datum -> ScriptContext -> Bool
checkTransfer Nothing _ _ _ _ _ _ = False
checkTransfer (Just vF) Nothing _ _ _ _ _ = False
checkTransfer (Just vF) (Just vT) from to val dat ctx = geq vF val && geq val 0 && from /= to &&
                         newDatum ctx == insert from (vF - val) (insert to (vT + val) dat)

{-# COMPILE AGDA2HS checkMembership #-}
{-# COMPILE AGDA2HS checkEmpty #-}
{-# COMPILE AGDA2HS checkWithdraw #-}
{-# COMPILE AGDA2HS checkDeposit #-}
{-# COMPILE AGDA2HS checkTransfer #-}

agdaValidator : Datum -> Input -> ScriptContext -> Bool
agdaValidator dat inp ctx = case inp of λ where
    (Open pkh) -> checkSigned pkh ctx && not (checkMembership (lookup pkh dat)) &&
                  newDatum ctx == insert pkh 0 dat && newValue ctx == oldValue ctx
    (Close pkh) -> checkSigned pkh ctx && checkEmpty (lookup pkh dat) &&
                   newDatum ctx == delete pkh dat && newValue ctx == oldValue ctx
    (Withdraw pkh val) -> checkSigned pkh ctx && checkWithdraw (lookup pkh dat) pkh val dat ctx &&
                          newValue ctx == oldValue ctx - val
    (Deposit pkh val) -> checkSigned pkh ctx && checkDeposit (lookup pkh dat) pkh val dat ctx &&
                         newValue ctx == oldValue ctx + val
    (Transfer from to val) -> checkSigned from ctx && 
                              checkTransfer (lookup from dat) (lookup to dat) from to val dat ctx &&
                              newValue ctx == oldValue ctx

{-# COMPILE AGDA2HS agdaValidator #-}

