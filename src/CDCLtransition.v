(* This file formalizes (Waldmann 2017) which does a good job
    on constructing a transition system on CDCL algorithm.
  http://rg1-teaching.mpi-inf.mpg.de/autrea-ws17/script.pdf, P29

*)

Inductive Literal (V : Set) : Set :=
  | pos : V -> Literal V
  | neg : V -> Literal V.

  
Definition Assignment (V:Set) := V -> bool.

(* Let's try an easy definition 
  on partial assignment first *)
Definition PAssignment (V:Set) := V -> option bool.

(* Assignment Stack records the decision point and partial assignment *)
Definition AssignmentStack (V: Set) := list ( (list (Literal V)) * PAssignment V).
(* The invariant include the later one must 
    have consistent assignment as the
    former ones
*)


Definition Clause (V : Set) := list (Literal V).
(* ListSet of Literals *)
Definition CNF (V: Set) := list (Clause V).
(* ListSet of CNF *)

Definition ClauseByAssignment {V} (c : Clause V)  (a : Assignment V): bool.
Admitted.
Definition ClauseByPAssignment {V} (c : Clause V) (a : PAssignment V): option bool.
Admitted.

Definition CNFByAssignment {V} (c : CNF V)  (a : Assignment V): bool.
Admitted.
Definition CNFByPAssignment {V} (c : CNF V) (a : PAssignment V): option bool.
Admitted.


Open Scope type_scope.
Open Scope list_scope.

Definition CDCLState {V : Set} :=  (AssignmentStack V) * (CNF V). 

(* Note that 
  CDCL are really doing proof search for undecdiability proof
  We can consider the invariant for each step here is that
    Assignment
*)

Inductive FinalState {V : Set} : CDCLState (V := V) -> Prop :=
  | failst : forall a c, (CNFByPAssignment c a = Some false) -> FinalState (a::nil, c)
  | succeedst : forall a b c, (CNFByPAssignment c a = Some true) -> FinalState (a::b, c).


(* We will have a non-determinism state transition machine
   We need to introduce monad to make/effect it "effect-free"
      (Maybe into a step : state -> Set(state))

   And make sure we have a terminating state transition.
    So let's first not focus on terminating

    Let's focus on satisfiable and unsatisfiability proof.
    Satisfiability is trivial.

    But Unsatisfiaibility is not, 
    we need to track the resolution proof as well

    We need to show the invariant that 
    Theorem 2.16 in (Waldmann 2017), basically
    N together with the guessing decision of literals 
        implies all the current literals 
*)
Inductive step {V : Set}: CDCLstate -> CDCLstate -> Prop :=
  | unit_prop :
      step (phi, M, ()) 


