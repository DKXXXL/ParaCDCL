(* This file formalizes (Waldmann 2017) which does a good job
    on constructing a transition system on CDCL algorithm.
  http://rg1-teaching.mpi-inf.mpg.de/autrea-ws17/script.pdf, P29

*)
Require Import src.rproof.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.

Open Scope type_scope.
Open Scope list_scope.

Definition ToLiteral {V: Set} `{EqDec_eq V} v (b : bool) : Literal V :=
  match b with 
  | true => positive v
  | false => negative v
  end.


Notation "t '[' x ':=' s ']' h" := (assign_pa x s t h) (at level 201).
Notation "∅" := empty_pa.

(* Assignment Stack records the decision point and partial assignment *)
(* The first PAssignment V is the guessed literal, the second is deduced literals *)
(* Definition AssignmentStack (V: Set) := list ( PAssignment V * PAssignment V). *)
(* 
Maintain the invariance that 
  AS f (g,d)
(f conj g) imply d
*)
(* We choose to use CNF to represent formula here
    but in the resolution proof we uses Formula V to represent formula
*)
Inductive AssignmentStack {V:Set} `{EqDec_eq V} (f : CNF V) : 
  list (PAssignment V * PAssignment V) -> Set :=
  | empty_as : AssignmentStack f ((∅,∅)::nil)
  | guess_as : forall {g} {d} x b {s},
      AssignmentStack f ((g, d)::s) ->
      forall (h : PA g x = None),
      AssignmentStack f (((g[x := b]h), d)::(g,d)::s) 
  | deduce_as : forall {g} {d} {s} x b,
      AssignmentStack f ((g, d)::s) ->
      forall (h : PA d x = None),
      RProof (fconj (CNFFormula f) (LiteralsForm g)) (flit (ToLiteral x b)) ->
      AssignmentStack f ((g, d[x := b]h)::s)
  | change_goal : forall {g} {s},
      AssignmentStack g s ->
      RProof (CNFFormula f) (CNFFormula g) ->
      AssignmentStack f s.  
(* change_goal is used to implement learn and forget *)
(* The invariant include the later one must 
  have consistent assignment as the
  former ones
*)

Notation AS := AssignmentStack.


Print eq_dec.

Proposition AssignmentStackHasRProof:
  forall {V : Set} `{EqDec_eq V} (f : CNF V) g d s,
    AS f ((g,d)::s) ->
    RProof (fconj (CNFFormula f) (LiteralsForm g)) (LiteralsForm d).
Admitted.

Proposition AssignmentStackCanWeaken:
  forall f g d,
  AS f s ->
  RProof h f ->
  AS h s.
Admitted.

Proposition AssignmentStackMonotoncity:
  forall f g d,
  AS f (t:s) ->
  AS f s.
Admitted.

Definition RProofInv {V} 
    (orginal : Formula V) 
    (guessedLiterals deducedLiterals: PAssignment V) := 
    RProof (conj orginal (LiteralsForm guessedLiterals)) (LiteralsForm deducedLiterals).  

Fixpoint RProofInvAStack {V}
    (original : Formula V)
    (astack : AssignmentStack V) : Prop := 
  match astack with
  | 

(* Definition CDCLState {V : Set} :=  (AssignmentStack V) * (CNF V).  *)

(* Note that 
  CDCL are really doing proof search for undecdiability proof
  We can consider the invariant for each step here is that
    Assignment
*)

(* Inductive FinalState {V : Set} : CDCLState (V := V) -> Prop :=
  | failst : forall a c, (CNFByPAssignment c a = Some false) -> FinalState (a::nil, c)
  | succeedst : forall a b c, (CNFByPAssignment c a = Some true) -> FinalState (a::b, c). *)

Definition SucceedState := .


Definition FailedState {V : Set} (st : AS f s)


Definition FinalState {V : Set} (st : AS f s) := SucceedState st \/ FailedState st.



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


Proposition step_with_proof:
  forall x y,
    step (astack, fx) (bstack, fy) ->



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


(* The following are the extracted functions *)

(* One step unit-prop *)

(* UnitProp until cannot *)

(* Guess One Literal *)

(* Check Failure *)

(* Back Jump *)