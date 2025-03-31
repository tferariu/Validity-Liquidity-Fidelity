module DEx where

data Label = Label{ratio :: Rational, owner :: PubKeyHash}

data Input = Update Integer Rational
           | Exchange Integer PubKeyHash
           | Close

data Params = Params{sellC :: AssetClass, buyC :: AssetClass}

checkPayment ::
             Params -> Integer -> Label -> PubKeyHash -> ScriptContext -> Bool
checkPayment par amt l pkh ctx
  = txOutAddress (getPaymentOutput (owner l) ctx) == owner l &&
      ratioCompare amt
        (amount (txOutValue (getPaymentOutput (owner l) ctx)))
        (ratio l)
        &&
        currency (txOutValue (getPaymentOutput (owner l) ctx)) == buyC par
          &&
          txOutDatum (getPaymentOutput (owner l) ctx) ==
            Payment (getSelf ctx)

checkBuyer ::
           Params -> Integer -> PubKeyHash -> ScriptContext -> Bool
checkBuyer par amt pkh ctx
  = txOutAddress (getPaymentOutput pkh ctx) == pkh &&
      txOutValue (getPaymentOutput pkh ctx) == Value amt (sellC par) &&
        txOutDatum (getPaymentOutput pkh ctx) == Payment (getSelf ctx)

agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator par l red ctx
  = case red of
        Update amt r -> checkSigned (owner l) ctx &&
                          checkRational r &&
                            newValue ctx == Value amt (sellC par) &&
                              newLabel ctx == Label r (owner l) && continuing ctx
        Exchange amt pkh -> oldValue ctx ==
                              newValue ctx <> Value amt (sellC par)
                              &&
                              newLabel ctx == l &&
                                checkPayment par amt l pkh ctx &&
                                  checkBuyer par amt pkh ctx && continuing ctx
        Close -> not (continuing ctx) && checkSigned (owner l) ctx

