module Decidable.Order

import Decidable.Decidable
import Decidable.Equality
import Data.RelationProperties


%access public

--------------------------------------------------------------------------------
-- Utility Lemmas
--------------------------------------------------------------------------------

--  FIXME change this title?
--------------------------------------------------------------------------------
-- Preorders and Posets
--------------------------------------------------------------------------------

class (Transitive t po, Reflexive t po) =>
  PreorderWeak t (po : t -> t -> Type)

class (PreorderWeak t lte0, Antisymmetric t lte0) =>
  PartialOrderWeak t (lte0 : t -> t -> Type)

--  Total order on top of PartialOrderWeak?

class (Transitive t po, Irreflexive t po) =>
  PreorderStrict t (po : t -> t -> Type)

class (PreorderStrict t lt0, Asymmetric t lt0) =>
  PartialOrderStrict t (lt0 : t -> t -> Type)
  
data Cmp : (t -> t -> Type) -> (a : t) -> (b : t) -> Type where
  cmpLT : (PartialOrderStrict t lt0) =>                    lt0 a b -> Cmp lt0 a b
  cmpEq : (PartialOrderStrict t lt0) => {a:t} -> {b:t} ->  (a = b) -> Cmp lt0 a b
  cmpGT : (PartialOrderStrict t lt0) =>                    lt0 b a -> Cmp lt0 a b

class (PartialOrderStrict t lt0) =>
  OrderStrict t (lt0 : t -> t -> Type) where
  total orderTotalStrict : (a : t) -> (b : t) -> Cmp lt0 a b

--  A 'safety corollary' for PartialOrder
--  - Wait a minute, should I be utilizing idris-mode magic here? (!!!)
--    - Well let me just try things in the old grueling way first.
--  FIXME does this belong somewhere else?
--total 
--notEqAndLT : (PartialOrder t ltT) => (a : t) -> (b : t) -> 
--             (a = b) -> ltT a b -> _|_
--notEqAndLT a a refl ltT = asymmetric a a ltT ltT

-- TODO adapt NatLTE etc. code to the new classes.

--------------------------------------------------------------------------------
-- Natural numbers
--------------------------------------------------------------------------------

data NatLT : Nat -> Nat -> Type where
  nLTsn     : NatLT n (S n)
  nLTmLTsm  : NatLT n m -> NatLT n (S m)

--  FIXME complete:
total
NatLTIsTransitive : (m : Nat) -> (n : Nat) -> (o : Nat) ->
                    NatLT m n -> NatLT n o -> NatLT m o

{-

data NatLTE : Nat -> Nat -> Type where
  nEqn   : NatLTE n n
  nLTESm : NatLTE n m -> NatLTE n (S m)

total NatLTEIsTransitive : (m : Nat) -> (n : Nat) -> (o : Nat) ->
                           NatLTE m n -> NatLTE n o ->
                           NatLTE m o
NatLTEIsTransitive m n n      mLTEn (nEqn) = mLTEn
NatLTEIsTransitive m n (S o)  mLTEn (nLTESm nLTEo)
  = nLTESm (NatLTEIsTransitive m n o mLTEn nLTEo)

total NatLTEIsReflexive : (n : Nat) -> NatLTE n n
NatLTEIsReflexive _ = nEqn

instance Preorder Nat NatLTE where
  transitive = NatLTEIsTransitive
  reflexive  = NatLTEIsReflexive

total NatLTEIsAntisymmetric : (m : Nat) -> (n : Nat) ->
                              NatLTE m n -> NatLTE n m -> m = n
NatLTEIsAntisymmetric n n nEqn nEqn = refl
NatLTEIsAntisymmetric n m nEqn (nLTESm _) impossible
NatLTEIsAntisymmetric n m (nLTESm _) nEqn impossible
NatLTEIsAntisymmetric n m (nLTESm _) (nLTESm _) impossible

instance Poset Nat NatLTE where
  antisymmetric = NatLTEIsAntisymmetric

total zeroNeverGreater : {n : Nat} -> NatLTE (S n) Z -> _|_
zeroNeverGreater {n} (nLTESm _) impossible
zeroNeverGreater {n}  nEqn      impossible

total
nGTSm : {n : Nat} -> {m : Nat} -> (NatLTE n m -> _|_) -> NatLTE n (S m) -> _|_
nGTSm         disprf (nLTESm nLTEm) = FalseElim (disprf nLTEm)
nGTSm {n} {m} disprf (nEqn) impossible

total
decideNatLTE : (n : Nat) -> (m : Nat) -> Dec (NatLTE n m)
decideNatLTE    Z      Z  = Yes nEqn
decideNatLTE (S x)     Z  = No  zeroNeverGreater
decideNatLTE    x   (S y) with (decEq x (S y))
  | Yes eq      = rewrite eq in Yes nEqn
  | No _ with (decideNatLTE x y)
    | Yes nLTEm = Yes (nLTESm nLTEm)
    | No  nGTm  = No (nGTSm nGTm)

instance Decidable [Nat,Nat] NatLTE where
  decide = decideNatLTE

lte : (m : Nat) -> (n : Nat) -> Dec (NatLTE m n)
lte m n = decide {ts = [Nat,Nat]} {p = NatLTE} m n

-}
