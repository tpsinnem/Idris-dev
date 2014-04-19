module Syntax.ImplicitDecisionArgs

import Data.DecYesNo

%default total

--------------------------------------------------
--  Syntax rules for Dec-based default arguments:
--------------------------------------------------

syntax "{{" [proofname] ":" "yes" [dec] "}}" "->" [ret] 
  = { default (decYes dec) proofname : decType dec } -> ret

syntax "{{" [proofname] ":" "no" [dec] "}}" "->" [ret] 
  = { default (decNo dec) proofname : decType dec -> _|_ } -> ret

-------------
--  Example:
-------------

{-

argsAreSame : (n:Nat) -> (m:Nat) -> {{ same : yes (decEq n m) }} -> ()
argsAreSame _ _ = ()

argsAreDiff : (n:Nat) -> (m:Nat) -> {{ diff : no (decEq n m) }} -> ()
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
