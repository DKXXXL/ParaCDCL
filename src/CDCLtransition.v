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
      forall (h : PA g x = None) (h2 : PA d x = None),
      AssignmentStack f (((g[x := b]h), d[x:=b]h2)::(g,d)::s) 
  | deduce_as : forall {g} {d} {s} x b,
      AssignmentStack f ((g, d)::s) ->
      forall (h : PA d x = None),
      RProof (fconj (CNFFormula f) (LiteralsFormPA g)) (flit (ToLiteral x b)) ->
      AssignmentStack f ((g, d[x := b]h)::s).
(* change_goal is used to implement learn and forget *)
(* The invariant include the later one must 
  have consistent assignment as the
  former ones
*)

Hint Constructors AssignmentStack.

Notation AS := AssignmentStack.


Theorem LiteralsFormPAcomm:
  forall {V: Set} `{EqDec_eq V} {g} {x : V} {b} {h},
    (LiteralsFormPA (g [x := b] h)) = fconj (flit (ToLiteral x b)) (LiteralsFormPA g).
  intros V H g.
  induction g; intros; cbn in *; eauto.
Qed.


Theorem PA_assign_comm:
  forall {V: Set} `{EqDec_eq V} {g : PAssignment V} {x b v h},
  PA (g [x := b] h) v =
    if (eq_dec v x) then Some b else PA g v.
  intros V h g.
  destruct g as [fg fp].
  induction fp; intros; cbn in *; eauto.
Qed.


Hint Constructors RProof.


Proposition AssignmentStackHasRProof:
  forall {V : Set} `{EqDec_eq V} (f : CNF V) g d s,
    AS f ((g,d)::s) ->
    RProof (fconj (CNFFormula f) (LiteralsFormPA g)) (LiteralsFormPA d).

intros V H f g d s. 
remember ((g, d) :: s) as s'.
intros h. 
generalize dependent g. generalize dependent d. generalize dependent s.
induction h; intros;
repeat match goal with
| [h : (?u :: ?v) = (?a :: ?b) |- _] =>
  inversion h; subst; cbn in *
end; 
repeat rewrite LiteralsFormPAcomm;
try (pose (IHh _ _ _ eq_refl)).
+ eauto. 
+ eapply rp_trans. eapply rp_comm_conj. eapply rp_weaken3.
  eauto.
+ eapply rp_rconj; eauto.
Qed.
 

Theorem AssignmentStackGSubD:
  forall {V : Set} `{EqDec_eq V} {f : CNF V} {g d s},
  AS f ((g, d) :: s) ->
  forall v T,
    PA g v = Some T ->
    PA d v = Some T.
  intros V H f g d s.
  remember ((g, d) :: s) as s'.
  intros h.
  generalize dependent g. generalize dependent d. generalize dependent s.
  induction h; intros; eauto;
  repeat match goal with
  | [h : (?u :: ?v) = (?a :: ?b) |- _] =>
  inversion h; subst; cbn in *
  end; 
eauto; 
repeat rewrite PA_assign_comm in *;
try match goal with 
  | [h : PA (?g [?x := ?b ] ?h0) ?v = _ |- _] =>
    rewrite PA_assign_comm in h
end;
match goal with 
| [|- context[eq_dec ?a ?b]] =>
  destruct (eq_dec a b); subst; eauto; try contradiction
end.
pose (IHh _ _ _ eq_refl _ _ H0) as Heqn.
clear Heqs'.
rewrite Heqn in *; 
match goal with 
| [h : Some _ = None |- _] => inversion h
end.
Qed.

Proposition AssignmentStackMonotoncity:
  forall f t s,
  AS f (t::s) ->
  s <> nil ->
  AS f s.

intros f t s. 
remember (t :: s) as s'.
intros h.
generalize dependent t. generalize dependent s.

induction h; intros;
repeat match goal with
| [h : (?u :: ?v) = (?a :: ?b) |- _] =>
  inversion h; subst; cbn in *
end; try contradiction; eauto.
Qed.

Theorem change_goal:
  forall {V:Set} `{EqDec_eq V} {g} {s} (f : CNF V),
    AssignmentStack g s ->
    RProof (CNFFormula f) (CNFFormula g) ->
    AssignmentStack f s.
  intros V H g s f h.
  generalize dependent f.
  induction h; intros; subst; eauto.
  pose (IHh _ H0). 
  eapply deduce_as; [eauto | idtac].
  eauto.
Qed.


(* 
Definition RProofInv {V : Set} `{EqDec_eq V} 
    (orginal : Formula V) 
    (guessedLiterals deducedLiterals: PAssignment V) := 
    RProof (fconj orginal (LiteralsFormPA guessedLiterals)) (LiteralsFormPA deducedLiterals).  

Fixpoint RProofInvAStack {V}
    (original : Formula V)
    (astack : AssignmentStack V) : Prop := 
  match astack with
  | nil => *)

(* Definition CDCLState {V : Set} :=  (AssignmentStack V) * (CNF V).  *)

(* Note that 
  CDCL are really doing proof search for undecdiability proof
  We can consider the invariant for each step here is that
    Assignment
*)

(* Inductive FinalState {V : Set} : CDCLState (V := V) -> Prop :=
  | failst : forall a c, (CNFByPAssignment c a = Some false) -> FinalState (a::nil, c)
  | succeedst : forall a b c, (CNFByPAssignment c a = Some true) -> FinalState (a::b, c). *)

Definition PeelOffPA {V : Set} `{EqDec_eq V} 
  {pa : PAssignment V} (h : forall x, PA pa x <> None) : 
  {f : V -> bool | forall x, PA pa x = Some (f x)}.
  
  refine 
  (exist _ (fun v =>
    match (PA pa v) with
    | Some k =>  k
    | None => true
    end ) _).
  intros. 
  destruct (PA pa x) eqn:hc; eauto.
  destruct (h _ hc).
Qed.

Definition FullPA {V : Set} `{EqDec_eq V} 
{pa : PAssignment V} (h : forall x, PA pa x <> None) :
  forall v, {result : bool | PA pa v = Some result } :=
  fun v =>
  let (fa, p2) := PeelOffPA h
  in let result  := fa v
  in  exist _ result (p2 v).

   



Definition SucceedState {V : Set} `{EqDec_eq V} {f s} (st : AS f s) : Prop := 
  match s with
  | nil => False
  | (_, d) :: _ => CNFByPAssignment f d = Some true
  end.
  


Definition FailedState {V : Set} `{EqDec_eq V} {f s} (st : AS f s) : Set :=
  RProof (CNFFormula f) fbot.



Definition FinalState {V : Set} `{EqDec_eq V} {f s} (st : AS f s) := FailedState st + {SucceedState st} .



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