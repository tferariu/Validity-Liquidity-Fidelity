open import DEx

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
import Data.Nat as N
open import Data.Integer.Base 
open import Data.Integer.Properties
open import Agda.Builtin.Int
open import Agda.Builtin.Nat renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Data.List hiding (lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base
import Data.Sign.Base as Sign

open import Data.Product using ( ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩; _×_ to _xx_)

open import Haskell.Prim hiding (⊥) 
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)
open import Haskell.Prelude using (lookup ; _<>_)


module DExProofs where


record Context : Set where
  field
    value         : Value  
    payVal        : Value
    payTo         : PubKeyHash
    payDat        : OutputDatum 
    buyVal        : Value
    buyTo         : PubKeyHash
    buyDat        : OutputDatum
    tsig          : PubKeyHash
    self          : Address
open Context


record State : Set where
  field
    label         : Label   
    context       : Context
    continues     : Bool 
open State


data _⊢_~[_]~>_ : Params -> State -> Input -> State -> Set where
 
  TUpdate : ∀ {amt r s s' par lab}
    -> label s ≡ lab
    -> owner lab ≡  tsig (context s')
    -> value (context s') ≡ record { amount = amt ; currency = sellC par }
    -> label s' ≡ (record { ratio = r ; owner = owner lab })
    -> checkRational r ≡ true 
    -> continues s ≡ true
    -> continues s' ≡ true
    -------------------
    -> par ⊢ s ~[ (Update amt r) ]~> s'


  TExchange : ∀ {amt pkh s s' par lab}
    -> value (context s) ≡ (value (context s')) <> record { amount = amt ; currency = sellC par }
    -> label s' ≡ label s
    -> label s ≡ lab 
    -> payTo (context s') ≡ (owner lab)
    -> amt * num (ratio lab) ≤ (amount (payVal (context s'))) * den (ratio lab) 
    -> currency (payVal (context s')) ≡ buyC par 
    -> payDat (context s') ≡ Payment (self (context s'))
    -> buyTo  (context s') ≡ pkh 
    -> buyVal (context s') ≡ record { amount = amt ; currency = sellC par }
    -> buyDat (context s') ≡ Payment (self (context s'))
    -> continues s ≡ true
    -> continues s' ≡ true
    -------------------
    -> par ⊢ s ~[ (Exchange amt pkh) ]~> s'

  TClose : ∀ {s s' par lab}
    -> label s ≡ lab 
    -> owner lab ≡ tsig (context s')
    -> continues s ≡ true
    -> continues s' ≡ false
    -------------------
    -> par ⊢ s ~[ Close ]~> s'


--Valid State
data ValidS : State -> Set where

  Stp : ∀ {s}
    -> continues s ≡ false
    ----------------
    -> ValidS s

  Oth : ∀ {s}
    -> checkRational (ratio (label s)) ≡ true 
    ----------------
    -> ValidS s


--Multi-Step Transition
data _⊢_~[_]~*_ : Params -> State -> List Input -> State -> Set where

  root : ∀ { s par }
    ------------------
    -> par ⊢ s ~[ [] ]~* s

  cons : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~> s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''


get⊥ : true ≡ false -> ⊥
get⊥ ()


selfContinuing : ∀ {s s' : State} {i par}
  -> i ≢ Close
  -> par ⊢ s ~[ i ]~> s'
  -> continues s' ≡ true
selfContinuing pf (TUpdate p1 p2 p3 p4 p5 p6 p7) = p7
selfContinuing pf (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) = p12
selfContinuing pf (TClose p1 p2 p3 p4) = ⊥-elim (pf refl)


noDoubleSatOut : ∀ {s s' : State} {i par amt pkh}
  -> i ≡ Exchange amt pkh
  -> par ⊢ s ~[ i ]~> s'
  -> (payDat (context s') ≡ Payment (self (context s')) × buyDat (context s') ≡ Payment (self (context s')))
noDoubleSatOut refl (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) = (p7 , p10)


--State Validity Invariant
validStateTransition : ∀ {s s' : State} {i par}
  -> ValidS s
  -> par ⊢ s ~[ i ]~> s'
  -> ValidS s'
validStateTransition {record { label = .( (record { ratio = ratio₁ ; owner = tsig context })) ; context = context₁ ; continues = .true }} {record { label = .( (record { ratio = _ ; owner = tsig context })) ; context = context ; continues = .true }} iv (TUpdate {lab = record { ratio = ratio₁ ; owner = .(tsig context) }} refl refl refl refl p5 refl refl) = Oth p5
validStateTransition (Stp x) (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) rewrite x = ⊥-elim (get⊥ (sym p11))
validStateTransition (Oth y) (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) rewrite sym p2 = Oth y
validStateTransition iv (TClose p1 p2 p3 p4) = Stp p4


validStateMulti : ∀ {s s' : State} {is par}
  -> ValidS s
  -> par ⊢ s ~[ is ]~* s'
  -> ValidS s'
validStateMulti iv root = iv
validStateMulti iv (cons pf x) = validStateMulti (validStateTransition iv pf) x



liquidity : ∀ (par : Params) (s : State) 
          -> ValidS s -> continues s ≡ true
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × (amount (value (context s')) ≡ 0) )
liquidity par s (Stp x) p2 rewrite p2 = ⊥-elim (get⊥ x)
liquidity par record { label = lab ; context = context ; continues = continues } (Oth y) p2 = ⟨ s' , ⟨  Close ∷ [] , (cons (TClose refl refl p2 refl ) root , refl) ⟩ ⟩
  where
    s' = record { label = (record { ratio = ratio lab ; owner = owner lab }) ;
                  context = record
                             { value = record { amount = 0 ; currency = sellC par }
                             ; payVal = (value (context))
                             ; payTo = (owner lab)
                             ; payDat = Payment 0
                             ; buyVal = record { amount = 0 ; currency = 0 }
                             ; buyTo = 0
                             ; buyDat = Payment 0
                             ; tsig = owner lab
                             ; self = self context
                             } ;
                  continues = false } 



go : ∀ (a : Bool) {b} -> (a && b) ≡ true -> b ≡ true
go true {b} pf = pf

get : ∀ {a b : Bool} -> (a && b) ≡ true -> a ≡ true
get {true} {true} pf = refl

==to≡ : ∀ {a b : Nat} -> (a == b) ≡ true -> a ≡ b
==to≡ {zero} {zero} p = refl
==to≡ {(Nat.suc a)} {(Nat.suc b)} p = cong Nat.suc (==to≡ p)

==ito≡ : ∀ {a b : Integer} -> (a == b) ≡ true -> a ≡ b
==ito≡ {(pos n)} {(pos m)} pf = cong (+_) (==to≡ pf)
==ito≡ {(negsuc n)} {(negsuc m)} pf = cong negsuc (==to≡ pf) 

==rto≡ : ∀ {a b : Rational} -> (a == b) ≡ true -> a ≡ b
==rto≡ {record { num = num ; den = den }} {record { num = num' ; den = den' }} pf
  rewrite ==ito≡ {num} {num'} (get pf) | ==ito≡ {den} {den'} (go (eqInteger num num') pf) = refl

unNot : ∀ {b : Bool} -> not b ≡ true -> b ≡ false
unNot {false} pf = refl

==lto≡ : ∀ (l l' : Label)
       -> (l == l') ≡ true
       -> l ≡ l' 
==lto≡ record { ratio = ratio ; owner = owner } record { ratio = ratio' ; owner = owner' } pf rewrite ==rto≡ {ratio} {ratio'} (get pf) | ==to≡ {owner} {owner'} (go (ratio == ratio') pf) = refl

neg≡ : ∀ (a : Integer) -> negateInteger a ≡ - a
neg≡ (pos zero) = refl
neg≡ +[1+ n ] = refl
neg≡ (negsuc zero) = refl
neg≡ (negsuc (N.suc n)) = refl

monusLT : ∀ (a b : Nat) -> ltNat a b ≡ true -> Internal.subNat a b ≡ - (+ monusNat b a)
monusLT zero (N.suc b) pf = refl
monusLT (N.suc a) (N.suc b) pf = monusLT a b pf

monusGT : ∀ (a b : Nat) -> ltNat a b ≡ false -> Internal.subNat a b ≡ + monusNat a b
monusGT zero zero pf = refl
monusGT (N.suc a) zero pf = refl
monusGT (N.suc a) (N.suc b) pf = monusGT a b pf

subN≡ : ∀ (a b : Nat) -> Internal.subNat a b ≡ a ⊖ b
subN≡ a b with ltNat a b in eq
...| true = monusLT a b eq
...| false = monusGT a b eq

add≡ : ∀ (a b : Integer) -> addInteger a b ≡ a + b
add≡ (+_ n) (+_ m) = refl
add≡ (+_ n) (negsuc m) = subN≡ n (N.suc m)
add≡ (negsuc n) (+_ m) = subN≡ m (N.suc n)
add≡ (negsuc n) (negsuc m) = refl


sign+≡ : ∀ (n : Nat) -> + n ≡ Sign.+ ◃ n
sign+≡ zero = refl
sign+≡ (N.suc n) = refl

sign-≡ : ∀ (n : Nat) -> Internal.negNat n ≡ Sign.- ◃ n
sign-≡ zero = refl
sign-≡ (N.suc n) = refl

mul≡ : ∀ (a b : Integer) -> mulInteger a b ≡ a * b
mul≡ (+_ n) (+_ m) = sign+≡ (mulNat n m)
mul≡ (+_ n) (negsuc m) = sign-≡ (mulNat n (N.suc m))
mul≡ (negsuc n) (+_ m) = sign-≡ (addNat m (mulNat n m))
mul≡ (negsuc n) (negsuc m) = refl


rewriteAdd : ∀ {a} (b c : Integer) -> a ≡ addInteger b c -> a ≡ b + c
rewriteAdd b c p rewrite add≡ b c = p

<=to≤ : ∀ {a b} -> (a N.<ᵇ b || a == b) ≡ true -> a N.≤ b
<=to≤ {zero} {zero} pf = N.z≤n
<=to≤ {zero} {suc b} pf = N.z≤n
<=to≤ {suc a} {suc b} pf = N.s≤s (<=to≤ pf)

≤≡lem : ∀ (a b : Nat) -> ltNat a (N.suc b) ≡ true -> (ltNat a b || eqNat a b) ≡ true
≤≡lem zero zero pf = refl
≤≡lem zero (N.suc b) pf = refl
≤≡lem (N.suc a) (N.suc b) pf = ≤≡lem a b pf

≤≡ : ∀ (a b : Nat) -> (a N.≤ᵇ b) ≡ true -> (ltNat a b || eqNat a b) ≡ true
≤≡ zero zero pf = refl
≤≡ zero (N.suc b) pf = refl
≤≡ (N.suc a) (N.suc b) pf = ≤≡lem a b pf

swapEqNat : ∀ (n m : Nat) -> eqNat n m ≡ eqNat m n
swapEqNat zero zero = refl
swapEqNat zero (N.suc m) = refl
swapEqNat (N.suc n) zero = refl
swapEqNat (N.suc n) (N.suc m) = swapEqNat n m

<=ito≤ : ∀ {a b : Integer} -> (ltInteger a b || eqInteger a b) ≡ true -> a ≤ b
<=ito≤ {pos n} {pos m} pf = +≤+ (<=to≤ pf)
<=ito≤ {negsuc n} {pos m} pf = -≤+
<=ito≤ {negsuc n} {negsuc m} pf rewrite swapEqNat n m = -≤- (<=to≤ pf)

getPayOutVal : Label -> ScriptContext -> Value
getPayOutVal l ctx = (txOutValue (getPaymentOutput (owner l) ctx))

getPayOutAdr : Label -> ScriptContext -> Address
getPayOutAdr l ctx = (txOutAddress (getPaymentOutput (owner l) ctx))

getPayOutDat : Label -> ScriptContext -> OutputDatum
getPayOutDat l ctx = (txOutDatum (getPaymentOutput (owner l) ctx))

getBuyOutVal : Label -> Input -> ScriptContext -> Value
getBuyOutVal l (Update r amt) ctx = record { amount = -1 ; currency = 0 }
getBuyOutVal l (Exchange amt pkh) ctx = (txOutValue (getPaymentOutput pkh ctx))
getBuyOutVal l Close ctx = record { amount = -1 ; currency = 0 }

getBuyOutAdr : Label -> Input -> ScriptContext -> Address
getBuyOutAdr l (Update r amt) ctx = 0
getBuyOutAdr l (Exchange amt pkh) ctx = (txOutAddress (getPaymentOutput pkh ctx))
getBuyOutAdr l Close ctx = 0

getBuyOutDat : Label -> Input -> ScriptContext -> OutputDatum
getBuyOutDat l (Update r amt) ctx = Payment 0
getBuyOutDat l (Exchange amt pkh) ctx = (txOutDatum (getPaymentOutput pkh ctx))
getBuyOutDat l Close ctx = Payment 0


==vto≡ : {a b : Value} -> (a == b) ≡ true -> a ≡ b
==vto≡ {record { amount = a1 ; currency = c1 }} {record { amount = a2 ; currency = c2 }} p
  rewrite (==ito≡ {a1} {a2} (get p)) | (==to≡ {c1} {c2} (go (a1 == a2) p)) = refl

rewriteMulCheck : ∀ (l : Label) (ctx : ScriptContext) (val) ->
  ((mulInteger val (num (ratio l))) <= (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx))) (den (ratio l)))) ≡ true ->
  (((sign val Sign.* sign (num (ratio l))) ◃ mulNat ∣ val ∣ ∣ num (ratio l) ∣) ≤
  ((sign (amount (txOutValue (getPaymentOutput (owner l) ctx))) Sign.* sign (den (ratio l))) ◃
  mulNat ∣ (amount (txOutValue (getPaymentOutput (owner l) ctx))) ∣ ∣ den (ratio l) ∣))
rewriteMulCheck l ctx val p rewrite mul≡ val (num (ratio l)) | mul≡ (amount (txOutValue (getPaymentOutput (owner l) ctx))) (den (ratio l)) = <=ito≤ p


5&&false : ∀ {a b c d e : Bool} -> e ≡ false -> (a && b && c && d && e) ≡ false
5&&false {false} {b} {c} {d} refl = refl
5&&false {true} {false} {c} {d} refl = refl
5&&false {true} {true} {false} {d} refl = refl
5&&false {true} {true} {true} {false} refl = refl
5&&false {true} {true} {true} {true} refl = refl

contradict : ∀ {b : Bool} -> b ≡ true -> b ≡ false -> ⊥
contradict refl ()

prop0 : ∀ {par l i ctx cs } -> purpose ctx ≡ Minting cs -> i ≢ Close -> agdaValidator par l i ctx ≡ false
prop0 {par} {l} {Update amt r} ctx@{record { txOutputs = [] ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = .(Minting _) }} refl p2 =  5&&false {checkSigned (owner l) ctx} {checkRational r} {newValue ctx == record { amount = amt ; currency = sellC par }} {newLabel ctx == (record {ratio = r ; owner = owner l})} refl
prop0 {par} {l} {Update amt r} ctx@{record { txOutputs = x ∷ txOutputs₁ ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = .(Minting _) }} refl p2 =  5&&false {checkSigned (owner l) ctx} {checkRational r} {newValue ctx == record { amount = amt ; currency = sellC par }} {newLabel ctx == (record {ratio = r ; owner = owner l})} refl
prop0 {par} {l} {Exchange amt pkh} ctx@{record { txOutputs = [] ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = .(Minting _) }} refl p2 = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} refl
prop0 {par} {l} {Exchange amt pkh} ctx@{record { txOutputs = x ∷ txOutputs₁ ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = .(Minting _) }} refl p2 = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} refl
prop0 {i = Close} p1 p2 = ⊥-elim (p2 refl)

prop : ∀ {par l i ctx} -> agdaValidator par l i ctx ≡ true -> i ≢ Close -> ∃[ adr ] purpose ctx ≡ Spending adr
prop {par} {l} {i} {ctx} p1 p2 with (purpose ctx) in eq
...| Spending adr' = ⟨ adr' , refl ⟩
...| Minting cs = ⊥-elim (contradict p1 (prop0 eq p2)) 

prop0' : ∀ {par l amt pkh ctx cs } -> purpose ctx ≡ Minting cs -> agdaValidator par l (Exchange amt pkh) ctx ≡ false
prop0' {par} {l} {amt} {pkh} ctx@{ctx = record { txOutputs = [] ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Minting x }} p = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} refl
prop0' {par} {l} {amt} {pkh} ctx@{ctx = record { txOutputs = x ∷ txOutputs ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Minting y }} p = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} refl

==dto≡ : {a b : OutputDatum} -> (a == b) ≡ true -> a ≡ b
==dto≡ {Payment x} {Payment y} p rewrite ==to≡ {x} {y} p = refl
==dto≡ {Script x} {Script y} p rewrite ==lto≡ x y p = refl

prop' : ∀ {par l amt pkh ctx} -> agdaValidator par l (Exchange amt pkh) ctx ≡ true ->  ∃[ adr ] (purpose ctx ≡ Spending adr × (txOutDatum (getPaymentOutput (owner l) ctx)) ≡ Payment adr)
prop' {par} {l} {amt} {pkh} ctx@{record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Spending adr }} p = ⟨ adr , (refl , ==dto≡ (go (currency (txOutValue (getPaymentOutput (owner l) ctx)) == buyC par) (go (ratioCompare amt (amount (txOutValue (getPaymentOutput (owner l) ctx))) (ratio l)) (go (txOutAddress (getPaymentOutput (owner l) ctx) == owner l) (get (go (newLabel ctx == l) (go (oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }) p))))))) ⟩
prop' {par} {l} {amt} {pkh} ctx@{record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Minting cs }} p = ⊥-elim (contradict p (prop0' {par} {l} {amt} {pkh} {ctx} {cs} refl))

prop'' : ∀ {par l amt pkh ctx} -> agdaValidator par l (Exchange amt pkh) ctx ≡ true ->  ∃[ adr ] (purpose ctx ≡ Spending adr × (txOutDatum (getPaymentOutput pkh ctx)) ≡ Payment adr)
prop'' {par} {l} {amt} {pkh} ctx@{record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Spending adr }} p = ⟨ adr , (refl , ==dto≡ (go ( (txOutValue (getPaymentOutput pkh ctx)) == record { amount = amt ; currency = sellC par }) (go (txOutAddress (getPaymentOutput pkh ctx) == pkh) (get (go (checkPayment par amt l pkh ctx) (go (newLabel ctx == l) (go (oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }) p))))))) ⟩
prop'' {par} {l} {amt} {pkh} ctx@{record { txOutputs = txOutputs ; inputVal = inputVal ; inputAc = inputAc ; signature = signature ; purpose = Minting cs }} p = ⊥-elim (contradict p (prop0' {par} {l} {amt} {pkh} {ctx} {cs} refl))


rewriteDatEq : ∀ {dat ctx} -> ∃[ adr ] (purpose ctx ≡ Spending adr × dat ≡ Payment adr) -> dat ≡ Payment (getSelf ctx)
rewriteDatEq {dat} {record { txOutputs = txOutputs₁ ; inputVal = inputVal₁ ; inputAc = inputAc₁ ; signature = signature₁ ; purpose = .(Spending adr) }} ⟨ adr , (refl , p2) ⟩ = p2

--Validator returning true implies transition relation is inhabited
validatorImpliesTransition : ∀ {pV pT pD bV bT bD sf s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : agdaValidator par l i ctx ≡ true)
                           -> par ⊢
                           record { label = l ; context = record { value = (inputVal ctx) ;
                           payVal = pV ; payTo = pT ; payDat = pD ;
                           buyVal = bV ; buyTo = bT ; buyDat = bD ;
                           tsig = s ; self = sf } ; continues = true }
                           ~[ i ]~>
                           record { label = newLabel ctx ; context = record { value = newValue ctx ;
                           payVal = getPayOutVal l ctx ; payTo = getPayOutAdr l ctx ; payDat = getPayOutDat l ctx  ;
                           buyVal = getBuyOutVal l i ctx ; buyTo = getBuyOutAdr l i ctx ; buyDat = getBuyOutDat l i ctx ;
                           tsig = signature ctx ; self = getSelf ctx} ; continues = continuing ctx}
validatorImpliesTransition par l (Update val r) ctx pf
  = TUpdate refl (==to≡ (get pf)) (==vto≡ (get (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))
  ((==lto≡ (newLabel ctx) (record { ratio = r ; owner = owner l }) (get (go
  (newValue ctx == record { amount = val ; currency = sellC par })
  (go (checkRational r) (go ((owner l) == (signature ctx)) pf))))))
  (get (go ((owner l) == (signature ctx)) pf)) refl (go (newLabel ctx == (record {ratio = r ; owner = owner l}))
  (go (newValue ctx == record { amount = val ; currency = sellC par }) (go (checkRational r)
  (go ((owner l) == (signature ctx)) pf))))
validatorImpliesTransition par l (Exchange amt pkh) ctx pf
  = TExchange (==vto≡ (get pf)) (==lto≡ (newLabel ctx) l
  (get (go (oldValue ctx == (newValue ctx) <> val) pf))) refl
  (==to≡ (get (get (go (newLabel ctx == l) (go (oldValue ctx == (newValue ctx) <> val) pf)))))
  (rewriteMulCheck l ctx amt (get (go ((txOutAddress (getPaymentOutput (owner l) ctx)) == (owner l))
  (get (go (newLabel ctx == l) ((go (oldValue ctx == (newValue ctx) <> val) pf)))))))
  (==to≡ (get (go (ratioCompare amt (amount (txOutValue (getPaymentOutput (owner l) ctx))) (ratio l))
  (go ((txOutAddress (getPaymentOutput (owner l) ctx)) == (owner l))
  (get (go (newLabel ctx == l) ((go (oldValue ctx == (newValue ctx) <> val) pf))))))))
  (rewriteDatEq {txOutDatum (getPaymentOutput (owner l) ctx)} {ctx} (prop' {par} {l} {amt} {pkh} {ctx} pf))
  (==to≡ (get (get (go (checkPayment par amt l pkh ctx) (go (newLabel ctx == l)
  (go (oldValue ctx == (newValue ctx) <> val) pf))))))
  (==vto≡ (get (go (txOutAddress (getPaymentOutput pkh ctx) == pkh)
  (get (go (checkPayment par amt l pkh ctx) (go (newLabel ctx == l)
  (go (oldValue ctx == (newValue ctx) <> val) pf)))))))
  ((rewriteDatEq {txOutDatum (getPaymentOutput pkh ctx)} {ctx} (prop'' {par} {l} {amt} {pkh} {ctx} pf)))
  refl
  (go (checkBuyer par amt pkh ctx) (go (checkPayment par amt l pkh ctx) (go (newLabel ctx == l)
  (go (oldValue ctx == (newValue ctx) <> val) pf))))
    where
      val = record { amount = amt ; currency = sellC par }
validatorImpliesTransition par l Close ctx pf
  = TClose refl (==to≡ (go (not (continuing ctx)) pf)) refl (unNot (get pf))


≡to== : ∀ {a b : Nat} -> a ≡ b -> (a == b) ≡ true
≡to== {zero} refl = refl
≡to== {suc a} refl = ≡to== {a} refl

n=n : ∀ (n : Nat) -> (n == n) ≡ true
n=n zero = refl
n=n (suc n) = n=n n

≡to==i : ∀ {a b : Integer} -> a ≡ b -> (a == b) ≡ true
≡to==i {pos n} refl = n=n n
≡to==i {negsuc n} refl = n=n n

i=i : ∀ (i : Int) -> (eqInteger i i) ≡ true
i=i (pos zero) = refl
i=i (pos (suc n)) = n=n n 
i=i (negsuc zero) = refl
i=i (negsuc (suc n)) = n=n n 

≡to==l : ∀ {a b : Label} -> a ≡ b -> (a == b) ≡ true
≡to==l {record { ratio = ratio ; owner = owner }} refl
  rewrite i=i (num ratio) | i=i (den ratio) | n=n owner = refl


≡to==v : ∀ {a b : Value} -> a ≡ b -> (a == b) ≡ true
≡to==v {a} {.a} refl rewrite i=i (amount a) | n=n (currency a) = refl

≤to<= : ∀ {a b : Nat} -> a N.≤ b -> (ltNat a b || eqNat a b) ≡ true
≤to<= {b = zero} N.z≤n = refl
≤to<= {b = N.suc b} N.z≤n = refl
≤to<= (N.s≤s p) = ≤to<= p

≤ito<= : ∀ {a b : Integer} -> a ≤ b -> (ltInteger a b || eqInteger a b) ≡ true
≤ito<= (-≤- {m} {n} n≤m) rewrite swapEqNat m n = ≤to<= n≤m
≤ito<= -≤+ = refl
≤ito<= (+≤+ m≤n) = ≤to<= m≤n

≡to==d : ∀ {a b : OutputDatum} -> a ≡ b -> (a == b) ≡ true
≡to==d {Payment x} refl rewrite n=n x = refl
≡to==d {Script x} refl rewrite n=n (owner x) | i=i (num (ratio x)) | i=i (den (ratio x)) = refl 

transitionImpliesValidator : ∀ {pV pT pD bV bT bD sf s} (par : Params) (l : Label) (i : Input) (ctx : ScriptContext)
                           -> (pf : par ⊢
                           record { label = l ; context = record { value = (inputVal ctx) ;
                           payVal = pV ; payTo = pT ; payDat = pD ; buyVal = bV ; buyTo = bT ; buyDat = bD ; tsig = s ; self = sf } ; continues = true }
                           ~[ i ]~>
                           record { label = newLabel ctx ; context = record { value = newValue ctx ;
                           payVal = getPayOutVal l ctx ; payTo = getPayOutAdr l ctx ; payDat = getPayOutDat l ctx  ;
                           buyVal = getBuyOutVal l i ctx ; buyTo = getBuyOutAdr l i ctx ; buyDat = getBuyOutDat l i ctx ;
                           tsig = signature ctx ; self = getSelf ctx} ; continues = continuing ctx})
                           -> agdaValidator par l i ctx ≡ true

transitionImpliesValidator par l (Update amt r) ctx (TUpdate refl p2 p3 p4 p5 p6 p7)
  rewrite ≡to== p2 | p5 | ≡to==v p3 | ≡to==l p4 = p7
transitionImpliesValidator par l (Exchange amt pkh) ctx (TExchange p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12)
  rewrite ≡to==v p1 | ≡to==l p2 | sym p3 | ≡to== p4 | mul≡ amt (num (ratio l)) |
  mul≡ (amount (txOutValue (getPaymentOutput (owner l) ctx))) (den (ratio l)) |
  ≤ito<= p5 | ≡to== p6 | ≡to== p8 | ≡to==v p9 | ≡to==d p10 | ≡to==d p7 = p12 
transitionImpliesValidator par l Close ctx (TClose p1 p2 p3 p4) rewrite p4 | p1 = ≡to== p2





rewriteContinuing : ∀ {ctx} -> getContinuingOutputs ctx ≡ [] -> continuing ctx ≡ false
rewriteContinuing p rewrite p = refl

prop1 : ∀ {par l i ctx} -> getContinuingOutputs ctx ≡ [] -> i ≢ Close -> agdaValidator par l i ctx ≡ false
prop1 {par} {l} {Update amt r} {ctx} p1 p2 = 5&&false {checkSigned (owner l) ctx} {checkRational r} {newValue ctx == record { amount = amt ; currency = sellC par }} {newLabel ctx == (record {ratio = r ; owner = owner l})} (rewriteContinuing {ctx} p1)
prop1 {par} {l} {Exchange amt pkh} {ctx} p1 p2 = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} (rewriteContinuing {ctx} p1)
prop1 {par} {l} {Close} {ctx} p1 p2 = ⊥-elim (p2 refl)

rewriteContinuing' : ∀ {ctx tx1 tx2 txs} -> getContinuingOutputs ctx ≡ (tx1 ∷ tx2 ∷ txs)  -> continuing ctx ≡ false
rewriteContinuing' p rewrite p = refl 

prop2 : ∀ {par l i ctx tx1 tx2 txs} -> getContinuingOutputs ctx ≡ (tx1 ∷ tx2 ∷ txs) -> i ≢ Close -> agdaValidator par l i ctx ≡ false
prop2 {par} {l} {Update amt r} {ctx} {tx1} {tx2} {txs} p1 p2 = 5&&false {checkSigned (owner l) ctx} {checkRational r} {newValue ctx == record { amount = amt ; currency = sellC par }} {newLabel ctx == (record {ratio = r ; owner = owner l})} (rewriteContinuing' {ctx} {tx1} {tx2} {txs} p1) 
prop2 {par} {l} {Exchange amt pkh} {ctx} {tx1} {tx2} {txs} p1 p2 = 5&&false {oldValue ctx == (newValue ctx) <> record { amount = amt ; currency = sellC par }} {newLabel ctx == l} {checkPayment par amt l pkh ctx} {checkBuyer par amt pkh ctx} (rewriteContinuing' {ctx} {tx1} {tx2} {txs} p1) 
prop2 {par} {l} {Close} {ctx} p1 p2 = ⊥-elim (p2 refl)



rwr : ∀ {amt l txo ctx}
  -> (ltInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue txo))
        (den (ratio l)))
       ||
       eqInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue txo))
        (den (ratio l)))) ≡ false
  -> (getPaymentOutput (owner l) ctx) ≡ txo
  -> (ltInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
        (den (ratio l)))
       ||
       eqInteger (mulInteger amt (num (ratio l)))
       (mulInteger (amount (txOutValue (getPaymentOutput (owner l) ctx)))
        (den (ratio l)))) ≡ false
rwr p1 refl = p1

