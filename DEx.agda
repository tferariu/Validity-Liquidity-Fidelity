module DEx where

open import Haskell.Prelude

PubKeyHash = Nat 
Address = Nat
CurrencySymbol = Nat
AssetClass = Nat

record Value : Set where
    field
            amount   : Integer
            currency : AssetClass
open Value public

addValue : Value -> Value -> Value
addValue a b = case currency a == currency b of λ where
  True -> record { amount = amount a + amount b ; currency = currency a }
  False -> a

eqValue : Value -> Value -> Bool
eqValue a b = (amount a == amount b) &&
              (currency a == currency b) 

instance
  iEqValue : Eq Value
  iEqValue ._==_ = eqValue
  
  iSemigroupValue : Semigroup Value
  iSemigroupValue ._<>_ = addValue

record Rational : Set where
    field
        num    : Integer
        den    : Integer
open Rational public

numerator : Rational -> Integer
numerator r = num r

denominator : Rational -> Integer
denominator r = den r

checkRational : Rational -> Bool
checkRational r = (numerator r >= 0) && (denominator r > 0)

Cmap = List ((Rational × PubKeyHash) × Integer)

record Label : Set where
  field
    ratio  : Rational
    owner  : PubKeyHash
open Label public

{-# COMPILE AGDA2HS Label #-}

eqRational : Rational -> Rational -> Bool
eqRational b c = (num b == num c) &&
                 (den b == den c) 


ltRational : Rational -> Rational -> Bool
ltRational b c = num b * den c < num c * den b

instance
  iEqRational : Eq Rational
  iEqRational ._==_ = eqRational

  iOrdRational : Ord Rational
  iOrdRational = ordFromLessThan ltRational


eqLabel : Label -> Label -> Bool
eqLabel b c = (ratio b == ratio c) &&
              (owner b == owner c)

instance
  iEqLabel : Eq Label
  iEqLabel ._==_ = eqLabel

data OutputDatum : Set where

  Payment : Address -> OutputDatum
  Script : Label -> OutputDatum

eqDatum : OutputDatum -> OutputDatum -> Bool
eqDatum (Payment x) (Payment y) = x == y
eqDatum (Payment x) (Script y) = False
eqDatum (Script x) (Payment y) = False
eqDatum (Script x) (Script y) = x == y

instance
  iEqDatum : Eq OutputDatum
  iEqDatum ._==_ = eqDatum

data ScriptPurpose : Set where

  Spending : Address -> ScriptPurpose
  Minting : CurrencySymbol -> ScriptPurpose

record TxOut : Set where
  field
    txOutAddress : Address
    txOutValue : Value
    txOutDatum : OutputDatum

open TxOut public

record ScriptContext : Set where
    field
        txOutputs   : List TxOut
        inputVal    : Value
        inputAc     : AssetClass
        signature   : PubKeyHash
        purpose     : ScriptPurpose
              
open ScriptContext public

checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == signature ctx

data Input : Set where
  Update   : Integer -> Rational -> Input
  Exchange : Integer -> PubKeyHash -> Input
  Close    : Input

{-# COMPILE AGDA2HS Input #-}

record Params : Set where
    field
            sellC  : AssetClass
            buyC   : AssetClass
open Params public

{-# COMPILE AGDA2HS Params #-}

getContinuingOutputs : ScriptContext -> List TxOut
getContinuingOutputs record { txOutputs = [] ; inputVal = inputVal ; inputAc = inputAc
                            ; signature = signature ; purpose = (Spending x) }
  = []
getContinuingOutputs record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; inputAc = inputAc
                            ; signature = signature ; purpose = (Spending adr) }
  = if adr == txOutAddress txO
       then txO ∷ getContinuingOutputs (record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc
                                                 ; signature = signature ; purpose = Spending adr })
       else getContinuingOutputs (record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc
                                           ; signature = signature ; purpose = Spending adr })
getContinuingOutputs record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc
                            ; signature = signature ; purpose = (Minting x) }
  = []

ownOutput : ScriptContext -> TxOut
ownOutput ctx = case (getContinuingOutputs ctx) of λ where
  (o ∷ []) -> o
  _ -> record { txOutAddress = 0 ; txOutValue = record { amount = -1 ; currency = 0 } ; txOutDatum = Payment 0 }

oldValue : ScriptContext -> Value
oldValue ctx = inputVal ctx

newLabel : ScriptContext -> Label
newLabel ctx = case txOutDatum (ownOutput ctx) of λ where
  (Script x) -> x
  _ -> record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }

newValue : ScriptContext -> Value
newValue ctx = txOutValue (ownOutput ctx)

aux : List TxOut -> Bool
aux txs = case txs of λ {
  (o ∷ []) -> True ;
  _ -> False }

continuing : ScriptContext -> Bool
continuing ctx = aux (getContinuingOutputs ctx)
  
ratioCompare : Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * (num r) <= b * (den r)

getPaymentOutput : Address -> ScriptContext -> TxOut
getPaymentOutput adr record { txOutputs = [] ; inputVal = inputVal ; signature = signature ; purpose = (Spending x) }
  = record { txOutAddress = 0 ; txOutValue = record { amount = -1 ; currency = 0 }
           ; txOutDatum = Script (record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }) }
getPaymentOutput adr record { txOutputs = (txO ∷ txOutputs) ; inputVal = inputVal ; inputAc = inputAc
                            ; signature = signature ; purpose = (Spending x) }
  = if txOutAddress txO == adr && txOutDatum txO == (Payment x)
       then txO
       else getPaymentOutput adr (record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc
                                 ; signature = signature ; purpose = (Spending x) })
getPaymentOutput adr record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc
                            ; signature = signature ; purpose = (Minting x) }
  = record { txOutAddress = 0 ; txOutValue = record { amount = -1 ; currency = 0 }
           ; txOutDatum = Script (record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }) }

aux' : ScriptPurpose -> Address
aux' p = case p of λ where
  (Minting cs) -> 0
  (Spending adr) -> adr

getSelf : ScriptContext -> Address
getSelf ctx = aux' (purpose ctx) 

checkPayment : Params -> Integer -> Label -> PubKeyHash -> ScriptContext -> Bool
checkPayment par amt l pkh ctx = txOutAddress (getPaymentOutput (owner l) ctx) == owner l &&
                                 ratioCompare amt (amount (txOutValue (getPaymentOutput (owner l) ctx))) (ratio l) &&
                                 currency (txOutValue (getPaymentOutput (owner l) ctx)) == buyC par &&
                                 txOutDatum (getPaymentOutput (owner l) ctx) == Payment (getSelf ctx)


{-# COMPILE AGDA2HS checkPayment #-}

checkBuyer : Params -> Integer -> PubKeyHash -> ScriptContext -> Bool
checkBuyer par amt pkh ctx = txOutAddress (getPaymentOutput pkh ctx) == pkh &&
                             (txOutValue (getPaymentOutput pkh ctx)) ==
                             record { amount = amt ; currency = sellC par }  &&
                             txOutDatum (getPaymentOutput pkh ctx) == Payment (getSelf ctx)

{-# COMPILE AGDA2HS checkBuyer #-}

agdaValidator : Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator par l red ctx = case red of λ where
  (Update amt r) -> checkSigned (owner l) ctx &&
                    checkRational r &&
                    newValue ctx == record { amount = amt ; currency = sellC par } && 
                    newLabel ctx == (record {ratio = r ; owner = owner l}) &&
                    continuing ctx
  (Exchange amt pkh) -> oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par } && 
                        newLabel ctx == l &&
                        checkPayment par amt l pkh ctx && checkBuyer par amt pkh ctx &&
                        continuing ctx
  Close -> not (continuing ctx) &&
           checkSigned (owner l) ctx

{-# COMPILE AGDA2HS agdaValidator #-} 
