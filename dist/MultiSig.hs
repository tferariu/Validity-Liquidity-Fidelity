module MultiSig where

import Numeric.Natural (Natural)

type Deadline = Natural

data Label = Holding
           | Collecting Value PubKeyHash Deadline [PubKeyHash]

data Input = Propose Value PubKeyHash Deadline
           | Add PubKeyHash
           | Pay
           | Cancel
           | Close

data Params = Params{authSigs :: [PubKeyHash], nr :: Natural,
                     maxWait :: Deadline}

query :: PubKeyHash -> [PubKeyHash] -> Bool
query pkh [] = False
query pkh (x : l') = x == pkh || query pkh l'

insert :: PubKeyHash -> [PubKeyHash] -> [PubKeyHash]
insert pkh [] = [pkh]
insert pkh (x : l')
  = if pkh == x then x : l' else x : insert pkh l'

agdaValidator :: Params -> Label -> Input -> ScriptContext -> Bool
agdaValidator param dat red ctx
  = case dat of
        Holding -> case red of
                       Propose v pkh d -> newValue ctx == oldValue ctx &&
                                            geq (oldValue ctx) v &&
                                              geq v minValue &&
                                                notTooLate param d ctx &&
                                                  continuing ctx &&
                                                    case newLabel ctx of
                                                        Holding -> False
                                                        Collecting v' pkh' d' sigs' -> v == v' &&
                                                                                         pkh == pkh'
                                                                                           &&
                                                                                           d == d'
                                                                                             &&
                                                                                             sigs'
                                                                                               == []
                       Add _ -> False
                       Pay -> False
                       Cancel -> False
                       Close -> gt minValue (oldValue ctx) && not (continuing ctx)
        Collecting v pkh d sigs -> case red of
                                       Propose _ _ _ -> False
                                       Add sig -> newValue ctx == oldValue ctx &&
                                                    checkSigned sig ctx &&
                                                      query sig (authSigs param) &&
                                                        continuing ctx &&
                                                          case newLabel ctx of
                                                              Holding -> False
                                                              Collecting v' pkh' d' sigs' -> v == v'
                                                                                               &&
                                                                                               pkh
                                                                                                 ==
                                                                                                 pkh'
                                                                                                 &&
                                                                                                 d ==
                                                                                                   d'
                                                                                                   &&
                                                                                                   sigs'
                                                                                                     ==
                                                                                                     insert
                                                                                                       sig
                                                                                                       sigs
                                       Pay -> lengthNat sigs >= nr param &&
                                                continuing ctx &&
                                                  case newLabel ctx of
                                                      Holding -> checkPayment pkh v ctx &&
                                                                   oldValue ctx == newValue ctx + v
                                                                     && checkSigned pkh ctx
                                                      Collecting _ _ _ _ -> False
                                       Cancel -> newValue ctx == oldValue ctx &&
                                                   continuing ctx &&
                                                     case newLabel ctx of
                                                         Holding -> expired d ctx
                                                         Collecting _ _ _ _ -> False
                                       Close -> False

