module Decidable.Order

import Decidable.Decidable
import Decidable.Equality

%access public

--------------------------------------------------------------------------------
-- Utility Lemmas
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Preorders and Posets
--------------------------------------------------------------------------------

class Preorder t (po : t -> t -> Type) where
  total transitive : (a : t) -> (b : t) -> (c : t) -> po a b -> po b c -> po a c
  total reflexive : (a : t) -> po a a

--class (Preorder t po) => Poset t (po : t -> t -> Type) where
--  total antisymmetric : (a : t) -> (b : t) -> po a b -> po b a -> a = b

-- FIXME THINK is this correct?
class (Preorder t lt) => PartialOrder t (lt : t -> t -> Type) where
  total antisymmetric : (a : t) -> (b : t) -> lt a b -> lt b a -> _|_

--  FIXME THINK do this via a 'Cmp' type instead of a bunch of negations?
--  - Can it work?

--  FIXME THINK how to have the order constraint here?
--  - Should 't' be an explicit argument?
--    - And then have the constraint down in the methods?
--  - Kinda side note: I think I'll end up assuming people downstream will use

--  FIXME In the methods, do I need to further specify the type of ltT? (!!)
--  - Or the types of a and b?
--  - Just try if this thing typechecks and save the fretting for later?

--data Cmp : (a : t) -> (b : t) -> Type where

--data Cmp : (t : Type) -> (a : t) -> (b : t) -> Type where
--  lt : (PartialOrder t ltT) =>  ltT a b -> Cmp t a b --  FIXME finish
--  eq : {a:t} -> {b:t}       ->  (a = b) -> Cmp t a b
--  gt : (PartialOrder t ltT) =>  ltT b a -> Cmp t a b

data Cmp : (t -> t -> Type) -> (a : t) -> (b : t) -> Type where
  lt : (PartialOrder t ltT) =>                    ltT a b -> Cmp ltT a b
  eq : (PartialOrder t ltT) => {a:t} -> {b:t} ->  (a = b) -> Cmp ltT a b
  gt : (PartialOrder t ltT) =>                    ltT b a -> Cmp ltT a b

--  FIXME do I need typeclass constraints in the orderTotal method or such?
--  FIXME why do I suddently feel like I wouldn't even need the PartialOrder
--    constraint here, and why does that smell like a code smell or worse?
--    - But is it a code smell or worse, or am I just prematurely scaredy?
--    - Are the requirements imposed by Cmp sufficient for the right behavior?
--    - In any case, I am at the moment kinda confused.
--    - How, exactly, might I get my head around a question of this sort? (!!)
--      - For one, if 'Cmp makes this sufficient', how do I argue that?
--    - Is there a prospect of not having the qualities that exist in Preorder
--      and PartialOrder?
--    - Does this evilly leave me free to choose different PartialOrders etc.
--      for different 'Cmp's? (!!)
--      - Will Cmp need to be parameterized [by [the PartialOrder instance]]
--        after all? (!!)
--        - This does seem kinda desirable, now that I think of it. (!!!)
--    - If my worries above are right, I feel just a little bit bad about even
--      going for a short while without being aware of a problem.
--    - BTW can I avoid having as much as four parameters on Cmp by not having
--      't' once I've added 'ltT'?

--class (PartialOrder t ltT) => Order t (ltT : t -> t -> Type) where
--  total orderTotal : (a : t) -> (b : t) -> Cmp t a b

--  FIXME again, do I need further specification of 'ltT'?
--  FIXME SANITY CHECK are 't' and 'ltT', in the methods, bound to the class parameters? (!!)
--  - Will the idris tutorial be enough for a clue or do I need to play around with this?
--  - I'm pretty sure they are thusly bound.
--  SANITY CHECK is the use of 'Cmp' the right thing to do here?
class (PartialOrder t ltT) => Order t (ltT : t -> t -> Type) where
  total orderTotal : (a : t) -> (b : t) -> Cmp ltT a b

-- TODO adapt everything below

--------------------------------------------------------------------------------
-- Natural numbers
--------------------------------------------------------------------------------

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
