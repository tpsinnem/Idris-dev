module Syntax.ImplicitDecisionArgs

import Data.DecProof

%default total

--------------------------------------------------
--  Syntax rules for Dec-based default arguments:
--------------------------------------------------

syntax "{{" [prfname] ":" "accept" [dec] "}}" "->" [ret] 
  = { default (decProof dec) prfname : DecType dec } -> ret

syntax "{{" [prfname] ":" "reject" [dec] "}}" "->" [ret] 
  = { default (decProof dec) prfname : DecType dec -> _|_ } -> ret

-------------
--  Example:
-------------

{-

argsAreSame : (n:Nat) -> (m:Nat) -> {{ same : accept (decEq n m) }} -> ()
argsAreSame _ _ = ()

argsAreDiff : (n:Nat) -> (m:Nat) -> {{ diff : reject (decEq n m) }} -> ()
argsAreDiff _ _ = ()

--  *Example> argsAreSame
--  argsAreSame : (n : Nat) -> (m : Nat) -> (n = m) -> ()
--
--  *Example> argsAreDiff
--  argsAreDiff : (n : Nat) -> (m : Nat) -> ((n = m) -> _|_) -> ()

zArgsAreSame : ()
zArgsAreSame = argsAreSame Z Z

zszArgsAreDiff : ()
zszArgsAreDiff = argsAreDiff Z (S Z)

-}
