module Data.DecProof

%default total

-----------------------------------------------
--  Manipulation of types and contents of Dec:
-----------------------------------------------

DecProofType : {a:Type} -> Dec a -> Type
DecProofType {a} (Yes _)  = a
DecProofType {a} (No _)   = a -> _|_

decProof : {a:Type} -> (dec : Dec a) -> DecProofType dec
decProof (Yes x)  = x
decProof (No x)   = x

DecType : {a:Type} -> Dec a -> Type
DecType {a} _ = a

