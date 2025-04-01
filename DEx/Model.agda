module DEx.Model where

open import Haskell.Prelude

CurrencySymbol = Nat
TokenName = Nat

PubKeyHash = Nat
Address = Nat

AssetClass = Nat

record Value : Set where
    field amount   : Integer
          currency : AssetClass
open Value public

addValue : Value → Value → Value
addValue a b = case currency a == currency b of λ where
  True → record { amount = amount a + amount b ; currency = currency a }
  False → a

eqValue : Value → Value → Bool
eqValue a b = (amount a == amount b) &&
              (currency a == currency b)

instance
  iEqValue : Eq Value
  iEqValue ._==_ = eqValue

  iSemigroupValue : Semigroup Value
  iSemigroupValue ._<>_ = addValue

record Rational : Set where
    field num    : Integer
          den    : Integer
open Rational public

numerator : Rational → Integer
numerator r = num r

denominator : Rational → Integer
denominator r = den r

checkRational : Rational → Bool
checkRational r = (numerator r >= 0) && (denominator r > 0)

Cmap = List ((Rational × PubKeyHash) × Integer)

record Label : Set where
  field ratio  : Rational
        owner  : PubKeyHash
open Label public

{-# COMPILE AGDA2HS Label #-}

eqRational : Rational → Rational → Bool
eqRational b c = (num b == num c) &&
                 (den b == den c)


ltRational : Rational → Rational → Bool
ltRational b c = num b * den c < num c * den b

instance
  iEqRational : Eq Rational
  iEqRational ._==_ = eqRational

instance
  iEqLabel : Eq Label
  iEqLabel ._==_ b c = (ratio b == ratio c) && (owner b == owner c)

data OutputDatum : Set where
  Payment : Address → OutputDatum
  Script  : Label   → OutputDatum

instance
  iEqDatum : Eq OutputDatum
  iEqDatum ._==_ = λ where
    (Payment x) (Payment y) → x == y
    (Payment x) (Script y)  → False
    (Script x)  (Payment y) → False
    (Script x)  (Script y)  → x == y

data ScriptPurpose : Set where
  Spending : Address        → ScriptPurpose
  Minting  : CurrencySymbol → ScriptPurpose

record TxOut : Set where
  field txOutAddress : Address
        txOutValue : Value
        txOutDatum : OutputDatum
open TxOut public

record ScriptContext : Set where
    field txOutputs : List TxOut
          inputVal  : Value
          inputAc   : AssetClass
          signature : PubKeyHash
          purpose   : ScriptPurpose
open ScriptContext public

checkSigned : PubKeyHash → ScriptContext → Bool
checkSigned sig ctx = sig == signature ctx

data Input : Set where
  Update   : Integer → Rational → Input
  Exchange : Integer → PubKeyHash → Input
  Close    : Input

{-# COMPILE AGDA2HS Input #-}

record Params : Set where
    field sellC : AssetClass
          buyC  : AssetClass
open Params public

{-# COMPILE AGDA2HS Params #-}

getContinuingOutputs : ScriptContext → List TxOut
getContinuingOutputs record { txOutputs = [] ; purpose = Spending x }
  = []
getContinuingOutputs ctx@record { txOutputs = o ∷ os; purpose = Spending adr }
  = let os = getContinuingOutputs (record ctx { txOutputs = os }) in
    if adr == o .txOutAddress then
      o ∷ os
    else
      os
getContinuingOutputs record { purpose = Minting x }
  = []

ownOutput : ScriptContext → TxOut
ownOutput ctx = case (getContinuingOutputs ctx) of λ where
  (o ∷ []) → o
  _ → record { txOutAddress = 0 ; txOutValue = record { amount = -1 ; currency = 0 } ; txOutDatum = Payment 0 }

oldValue : ScriptContext → Value
oldValue ctx = inputVal ctx

newLabel : ScriptContext → Label
newLabel ctx = case txOutDatum (ownOutput ctx) of λ where
  (Script x) → x
  _ → record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }

newValue : ScriptContext → Value
newValue ctx = txOutValue (ownOutput ctx)

isSingleton : ∀ {A : Set} → List A → Bool
isSingleton xs = case xs of λ where
  (_ ∷ []) → True
  _        → False

continuing : ScriptContext → Bool
continuing ctx = isSingleton (getContinuingOutputs ctx)

ratioCompare : Integer → Integer → Rational → Bool
ratioCompare a b r = a * (num r) <= b * (den r)


getPaymentOutput : Address → ScriptContext → TxOut
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


getSelf' : ScriptPurpose → Address
getSelf' p = case p of λ where
  (Minting cs) → 0
  (Spending adr) → adr

getSelf : ScriptContext → Address
getSelf ctx = getSelf' (purpose ctx)

checkPayment : Params → Integer → Label → PubKeyHash → ScriptContext → Bool
checkPayment par amt l pkh ctx
  =  txOutAddress (getPaymentOutput (owner l) ctx) == owner l
  && ratioCompare amt (amount (txOutValue (getPaymentOutput (owner l) ctx))) (ratio l)
  && currency (txOutValue (getPaymentOutput (owner l) ctx)) == buyC par
  && txOutDatum (getPaymentOutput (owner l) ctx) == Payment (getSelf ctx)

{-# COMPILE AGDA2HS checkPayment #-}

checkBuyer : Params → Integer → PubKeyHash → ScriptContext → Bool
checkBuyer par amt pkh ctx
  = txOutAddress (getPaymentOutput pkh ctx) == pkh
  && (txOutValue (getPaymentOutput pkh ctx)) == record { amount = amt ; currency = sellC par }
  && txOutDatum (getPaymentOutput pkh ctx) == Payment (getSelf ctx)

{-# COMPILE AGDA2HS checkBuyer #-}

agdaValidator : Params → Label → Input → ScriptContext → Bool
agdaValidator par l red ctx = case red of λ where
  (Update amt r)     → checkSigned (owner l) ctx
                    && checkRational r
                    && newValue ctx == record { amount = amt ; currency = sellC par }
                    && newLabel ctx == (record {ratio = r ; owner = owner l})
                    && continuing ctx
  (Exchange amt pkh) → oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }
                    && newLabel ctx == l
                    && checkPayment par amt l pkh ctx
                    && checkBuyer par amt pkh ctx
                    && continuing ctx
  Close              → not (continuing ctx)
                    && checkSigned (owner l) ctx

{-# COMPILE AGDA2HS agdaValidator #-}
