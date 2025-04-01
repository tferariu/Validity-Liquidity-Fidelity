module AccountSim.Model where

open import Haskell.Prelude

PubKeyHash     = Integer
Value          = Integer

Label = List (PubKeyHash × Value)
{-# COMPILE AGDA2HS Label #-}

record ScriptContext : Set where
  field inputVal    : Integer
        outputVal   : Integer
        outputLabel : Label
        signature   : PubKeyHash
open ScriptContext public

data Input : Set where
  Open     : PubKeyHash → Input
  Close    : PubKeyHash → Input
  Withdraw : PubKeyHash → Value → Input
  Deposit  : PubKeyHash → Value → Input
  Transfer : PubKeyHash → PubKeyHash → Value → Input
{-# COMPILE AGDA2HS Input #-}

insert : PubKeyHash → Value → Label → Label
insert pkh val = λ where
  [] → (pkh , val) ∷ []
  ((x , y) ∷ xs) →
    if pkh == x then
      (pkh , val) ∷ xs
    else
      (x , y) ∷ insert pkh val xs
{-# COMPILE AGDA2HS insert #-}

delete : PubKeyHash → Label → Label
delete pkh = λ where
  [] → []
  ((x , y) ∷ xs) →
    if pkh == x then
      xs
    else
      (x , y) ∷ delete pkh xs
{-# COMPILE AGDA2HS delete #-}

newLabel : ScriptContext → Label
newLabel = outputLabel

oldValue newValue : ScriptContext → Value
oldValue = inputVal
newValue = outputVal

geq gt : Value → Value → Bool
geq = _>=_
gt  = _>_

emptyValue minValue : Value
emptyValue = 0
minValue   = 2

checkSigned : PubKeyHash → ScriptContext → Bool
checkSigned pkh ctx = pkh == signature ctx

checkMembership' : PubKeyHash → Label → Bool
checkMembership' pkh lab = case lookup pkh lab of λ where
  Nothing → False
  (Just v) → True

checkMembership : Maybe Value → Bool
checkMembership Nothing = False
checkMembership (Just v) = True
{-# COMPILE AGDA2HS checkMembership #-}

checkEmpty : Maybe Value → Bool
checkEmpty Nothing = False
checkEmpty (Just v) = v == emptyValue
{-# COMPILE AGDA2HS checkEmpty #-}

checkWithdraw : Maybe Value → PubKeyHash → Value → Label → ScriptContext → Bool
checkWithdraw Nothing _ _ _ _ = False
checkWithdraw (Just v) pkh val lab ctx = geq val emptyValue && geq v val && (newLabel ctx == insert pkh (v - val) lab)
{-# COMPILE AGDA2HS checkWithdraw #-}

checkDeposit : Maybe Value → PubKeyHash → Value → Label → ScriptContext → Bool
checkDeposit Nothing _ _ _ _ = False
checkDeposit (Just v) pkh val lab ctx = geq val emptyValue && (newLabel ctx == insert pkh (v + val) lab)
{-# COMPILE AGDA2HS checkDeposit #-}

checkTransfer : Maybe Value → Maybe Value → PubKeyHash → PubKeyHash → Value → Label → ScriptContext → Bool
checkTransfer Nothing _ _ _ _ _ _ = False
checkTransfer (Just vF) Nothing _ _ _ _ _ = False
checkTransfer (Just vF) (Just vT) from to val lab ctx = geq vF val && geq val 0 && from /= to &&
                         newLabel ctx == insert from (vF - val) (insert to (vT + val) lab)
{-# COMPILE AGDA2HS checkTransfer #-}

agdaValidator : Label → Input → ScriptContext → Bool
agdaValidator lab inp ctx = case inp of λ where
    (Open pkh)            → checkSigned pkh ctx
                         && not (checkMembership (lookup pkh lab))
                         && newLabel ctx == insert pkh 0 lab
                         && newValue ctx == oldValue ctx

    (Close pkh)            → checkSigned pkh ctx
                          && checkEmpty (lookup pkh lab)
                          && newLabel ctx == delete pkh lab
                          && newValue ctx == oldValue ctx

    (Withdraw pkh val)     → checkSigned pkh ctx
                          && checkWithdraw (lookup pkh lab) pkh val lab ctx
                          && newValue ctx == oldValue ctx - val

    (Deposit pkh val)      → checkSigned pkh ctx
                          && checkDeposit (lookup pkh lab) pkh val lab ctx
                          && newValue ctx == oldValue ctx + val

    (Transfer from to val) → checkSigned from ctx
                          && checkTransfer (lookup from lab) (lookup to lab) from to val lab ctx
                          && newValue ctx == oldValue ctx

{-# COMPILE AGDA2HS agdaValidator #-}
