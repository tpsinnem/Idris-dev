module Data.YesNo

%default total

-----------------------------------------------
--  Manipulation of types and contents of Dec:
-----------------------------------------------

decType : {a:Type} -> Dec a -> Type
decType {a} _ = a


data BadDecYes : Type -> Type where
  badDecYes  : {A:Type} -> (A)        -> BadDecYes A

data BadDecNo : Type -> Type where
  badDecNo   : {A:Type} -> (A -> _|_) -> BadDecNo A


decYesType : {A:Type} -> Dec A -> Type
decYesType {A} (Yes _)  = A
decYesType {A} (No _)   = BadDecNo A

decNoType : {A:Type} -> Dec A -> Type
decNoType {A} (Yes _)   = BadDecYes A
decNoType {A} (No _)    = A -> _|_


decYes : {A:Type} -> (dec : Dec A) -> decYesType dec
decYes (Yes a) = a
decYes (No a)  = badDecNo a

decNo : {A:Type} -> (dec : Dec A) -> decNoType dec
decNo (Yes a)  = badDecYes a
decNo (No a)   = a

