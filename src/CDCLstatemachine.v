
(* We start with
    specification of stepAS : AS f x -> AS f y -> Prop
    which models all the operation AS_spec

    This should be plausible to prove the termination
*)


(* Specification of step : CDCLState f -> CDCLState f -> Prop
  1. step is terminating


  I will relax proving 1, by only proving 1 
    in the version of stepAS
      (unless I have time later)
  for 2 and 3, the correspondent in stepAS will also be proved
    as lemma
*)


Inductive step  {f : CNF V}: 
  CDCLState f -> CDCLState f -> Prop := 
  | unit_prop :
      step (existT _ (existT _ ))


(* This is not so important but
    we have a partial ordering on Assignment Stack
    and if we have finite number of variables
    i.e. V is of finite size, 
    then we have, for every chain, a "largest" stack

    This is not important because it is just a theorem/verification
     we need to prove 

    It will disappear after extraction.

    The important is the four theorem that act as small-step transition
    Basically unit prop, decide, checkFail, and backjump.

    We might need to add more
    *)
Proposition Terminating:
  forall x y,
    steps x y ->
    exists z,
    steps y z /\ FinalState z.
Admitted.

