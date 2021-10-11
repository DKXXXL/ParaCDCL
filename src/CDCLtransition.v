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


Section CDCLtransition.



Context {V:Set}.

Context {H: EqDec_eq V}.



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
The specfication for assignment stack is that
  the invariance of 
    {AS f ((g,d)::s) ->
    RProof (fconj f g) d}
  holds all the time 
    *)
Inductive AssignmentStack (f : CNF V) : 
  list (PAssignment V * PAssignment V) -> Set :=
  | empty_as : AssignmentStack f ((∅,∅)::nil)
  | guess_as : forall {g} {d} x b {s},
      AssignmentStack f ((g, d)::s) ->
      forall (h : PA g x = None) (h2 : PA d x = None),
      AssignmentStack f (((g[x := b]h), d[x:=b]h2)::(g,d)::s) 
  (* Decide *)
  | deduce_as : forall {g} {d} {s} x b,
      AssignmentStack f ((g, d)::s) ->
      forall (h : PA d x = None),
      RProof (fconj (CNFFormula f) (LiteralsFormPA g)) (flit (ToLiteral x b)) ->
      AssignmentStack f ((g, d[x := b]h)::s).
  (* Unit Prop *)
(* change_goal is used to implement learn and forget *)
(* The invariant include the later one must 
  have consistent assignment as the
  former ones
*)

Hint Constructors AssignmentStack.

Notation AS := AssignmentStack.


Theorem LiteralsFormPAcomm:
  forall  {g} {x : V} {b} {h},
    (LiteralsFormPA (g [x := b] h)) = fconj (flit (ToLiteral x b)) (LiteralsFormPA g).
  intros g.
  induction g; intros; cbn in *; eauto.
Qed.


Theorem PA_assign_comm:
  forall  {g : PAssignment V} {x b v h},
  PA (g [x := b] h) v =
    if (eq_dec v x) then Some b else PA g v.
  intros g.
  destruct g as [fg fp].
  induction fp; intros; cbn in *; eauto.
Qed.


Hint Constructors RProof.


Proposition AssignmentStackHasRProof:
  forall  {f : CNF V} {g d s},
    AS f ((g,d)::s) ->
    RProof (fconj (CNFFormula f) (LiteralsFormPA g)) (LiteralsFormPA d).

intros f g d s. 
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
  forall  {f : CNF V} {g d s},
  AS f ((g, d) :: s) ->
  forall v T,
    PA g v = Some T ->
    PA d v = Some T.
  intros f g d s.
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
  forall  {f : CNF V} { t s},
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

Proposition AssignmentStackMonotoncity2:
  forall  {f : CNF V} {k s},
  AS f (k ++ s) ->
  s <> nil ->
  AS f s.

intros f k.
generalize dependent f.
induction k; intros; subst; eauto.

rewrite <- List.app_comm_cons in *.
eapply IHk; eauto.
eapply AssignmentStackMonotoncity; eauto.
intro hh.
destruct (List.app_eq_nil _ _ hh); subst; try contradiction.
Qed.


Theorem change_goal:
  forall  {g} {s} (f : CNF V),
    AssignmentStack g s ->
    RProof (CNFFormula f) (CNFFormula g) ->
    AssignmentStack f s.
  intros g s f h.
  generalize dependent f.
  induction h; intros; subst; eauto.
  pose (IHh _ H0). 
  eapply deduce_as; [eauto | idtac].
  eauto.
Qed.


(* 
Definition RProofInv  
    (orginal : Formula V) 
    (guessedLiterals deducedLiterals: PAssignment V) := 
    RProof (fconj orginal (LiteralsFormPA guessedLiterals)) (LiteralsFormPA deducedLiterals).  

Fixpoint RProofInvAStack {V}
    (original : Formula V)
    (astack : AssignmentStack V) : Prop := 
  match astack with
  | nil => *)


(* Note that 
  CDCL are really doing proof search for undecdiability proof
  We can consider the invariant for each step here is that
    Assignment
*)

(* Inductive FinalState {V : Set} : CDCLState (V := V) -> Prop :=
  | failst : forall a c, (CNFByPAssignment c a = Some false) -> FinalState (a::nil, c)
  | succeedst : forall a b c, (CNFByPAssignment c a = Some true) -> FinalState (a::b, c). *)

Definition PeelOffPA  
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

Definition FullPA  
{pa : PAssignment V} (h : forall x, PA pa x <> None) :
  forall v, {result : bool | PA pa v = Some result } :=
  fun v =>
  let (fa, p2) := PeelOffPA h
  in let result  := fa v
  in  exist _ result (p2 v).

   


Corollary AssignmentStackGSubD2:
  forall  {f : CNF V} {g d s},
  AS f ((g, d) :: s) ->
  forall v,
    PA d v = None ->
    PA g v = None.
  intros f g d s h0 v hh.
  pose (AssignmentStackGSubD h0) as h1.
  destruct (PA g v) eqn:Heq2; subst; eauto.
  pose (h1 _ _ Heq2) as h3.
  rewrite h3 in hh; try inversion hh.
Qed.
    

(* | guess_as : forall {g} {d} x b {s},
AssignmentStack f ((g, d)::s) ->
forall (h : PA g x = None) (h2 : PA d x = None),
AssignmentStack f (((g[x := b]h), d[x:=b]h2)::(g,d)::s)  *)




(* Now we should be able to construct the four basic methods
    unit_propagation, decide, fail, backjump
*)

Definition VofLiteral {V : Set} (l : Literal V) : V :=
  match l with
  | positive x => x
  | negative x => x
  end.

Definition PolarityofLiteral {V : Set} (l : Literal V) : bool :=
  match l with
  | positive x => true
  | negative x => false
  end.

Axiom rp_byassign1:
  forall {c d},
  ClauseByPAssignment c d = Some true ->
  RProof (LiteralsFormPA d) (ClauseFormula c).

Axiom rp_byassign2:
  forall {c d},
  ClauseByPAssignment c d = Some false ->
  RProof (LiteralsFormPA d) (fneg (ClauseFormula c)).


Axiom rp_res:
  forall {X Y Z : Formula V},
  RProof X (fdisj Y Z) ->
  RProof X (fneg Z) ->
  RProof X Y.

Definition unit_prop_AS_spec: forall  {l c g d s f x b},
  (*
    We later need to relax this - l doesn't have to be the first
    term; l::c doesn't have to be the first term
  *)
  AS ((l::c)::f) ((g,d) :: s) -> 
  l = ToLiteral x b ->
  (* eval C under d = false -> *)
  ClauseByPAssignment c d = Some false ->
  (* PA d l = None -> *)
  forall (h : PA d x = None),
  AS ((l::c)::f) ((g,d[x := b]h) :: s).
  intros. eapply deduce_as; [eauto | idtac].
  pose (AssignmentStackHasRProof H0) as HH0. cbn in *.
  match goal with
  | [HH0 := _ : RProof (fconj (fconj ?a ?d) ?b) ?c |- _] =>
      assert (RProof (fconj (fconj a d) b) a) as HH1
  end; subst;
  [eapply rp_trans; eapply rp_weaken | idtac].
  pose (rp_byassign2 H2) as HH3.
  pose (rp_trans HH0 HH3) as HH4.
  pose (rp_res HH1 HH4) as HH5. auto.
Qed.

(* TODO: prove it by crush *)

Definition decide_AS_spec  {f g d s} x b 
  (stack : AS f ((g, d)::s)) 
  (h : PA d x = None) :
  AS f (((g[x := b](AssignmentStackGSubD2 stack _ h)), d[x:=b] h)::(g,d)::s).
  eauto.
Defined.

Lemma AS_no_guessing:
  forall {f g d},
  AS f ((g, d) :: nil) ->
  g = ∅.
intros f g d. remember ((g, d) :: nil) as s.
intros H0. generalize dependent g. generalize dependent d.
induction H0; intros; subst; eauto; try discriminate; try contradiction;
match goal with 
| [h : ?a::?b = ?c::?d |- _] =>
    inversion h; intros; subst; eauto 
end.
Qed.



Definition fail_AS_spec: forall {c f g d},
  AS (c::f) ((g, d) ::nil) ->
  ClauseByPAssignment c d = Some false ->
  RProof (CNFFormula (c:: f)) fbot.


intros c f g d H0 H1.
pose (AS_no_guessing H0) as HH'. 
generalize HH'. intros HH. clear HH'. subst.
pose (AssignmentStackHasRProof H0) as H2.
pose (rp_byassign2 H1) as H3. cbn in *.
pose (rp_trans H2 H3) as H4.
eapply rp_trans; [idtac | eapply rp_contra]; eauto.
Qed.

Theorem PA_consistent_with_A:
  forall {f pa g},
    CNFByPAssignment f pa <> None ->
    (forall x, 
        PA pa x <> None ->
        PA pa x = Some (g x)
      ) ->
      CNFByPAssignment f pa = Some (CNFByAssignment f g).
Admitted.

Definition extendPA (pa : PAssignment V) : Assignment V := 
  fun v =>
    match PA pa v with
    | Some k => k
    | None => true
    end.

Corollary PA_consistent_with_ExtendedA:
  forall {f pa},
  CNFByPAssignment f pa <> None ->
  CNFByPAssignment f pa = Some (CNFByAssignment f (extendPA pa)).
  intros; eapply PA_consistent_with_A; eauto.
  unfold extendPA. intros; destruct (PA pa x); subst; eauto; try discriminate; try contradiction.
Qed.




Definition succeed_AS_spec: forall {f g d s},
  AS f ((g, d) ::s) ->
  CNFByPAssignment f d = Some true ->
  {g2 | CNFByAssignment f g2 = true}.
intros f g d s H0 H1. exists (extendPA d).
assert (CNFByPAssignment f d <> None) as H2. repeat rewrite H1 in *.
intro; try discriminate; try contradiction.
pose (PA_consistent_with_ExtendedA H2) as H3.
rewrite H3 in H1. inversion H1; subst; eauto.
Qed.


Axiom rp_byassign4:
  forall {c d},
  FormulaByPAssignment c d = Some false ->
  RProof (LiteralsFormPA d) (fneg c).

Axiom rp_comm_disj:
  forall {X Y Z : Formula V},
  RProof X (fdisj Y Z) ->
  RProof X (fdisj Z Y).


Definition backjump_AS_spec: forall  {f C k g d s l} x b,
  (*
    We later need to relax this - l doesn't have to be the first
    term; l::c doesn't have to be the first term
  *)
  AS f (k ++ (g,d) :: s) -> 
  l = ToLiteral x b ->
  (* f ⊧ C ∨ l*)
  RProof (CNFFormula f) (fdisj C (flit l)) ->
  (* eval C under d = false -> *)
  FormulaByPAssignment C d = Some false ->
  (* PA d l = None -> *)
  forall (h : PA d x = None),
  AS f ((g,d[x := b]h) :: s).

intros f C k g d s l x b h0. 

assert (AS f ((g,d) :: s)) as H0; try eapply AssignmentStackMonotoncity2; try eapply h0.
intro HC. inversion HC. 
assert (RProof (fconj (CNFFormula f) (LiteralsFormPA g)) (LiteralsFormPA d)) as H2; try eapply AssignmentStackHasRProof; eauto.
intros h1 h2 h3 h.
assert (RProof (LiteralsFormPA d) (fneg C)) as H4; try eapply rp_byassign4; eauto.
assert (RProof (fconj (CNFFormula f) (LiteralsFormPA g)) (fneg C)) as H5; eauto.
assert (RProof (fconj (CNFFormula f) (LiteralsFormPA g)) (fdisj C (flit l))) as H6; eauto.
assert (RProof (fconj (CNFFormula f) (LiteralsFormPA g))  (flit l)) as H7.
+ eapply rp_res; [idtac | eauto]. eapply rp_comm_disj. eauto.
+ subst. eauto.
Qed. 


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


(* 
Definition SucceedAS  {f s} (st : AS f s) : Prop := 
    match s with
    | nil => False
    | (_, d) :: _ => CNFByPAssignment f d = Some true
    end.
  
Definition FailedAS  {f s} (st : AS f s) : Set :=
    RProof (CNFFormula f) fbot.

Definition FinalAS  {f s} (st : AS f s) := FailedState st + {SucceedState st} .
   *)




(* A CDCL state targeting to solve formula f
      g is the learned clauses
      s is the current assignment stack
*)
Definition CDCLState  (f : CNF V) :=  
  {learned & {s & (AS (learned ++ f) s) * RProof (CNFFormula f) (CNFFormula learned)} }. 

(* This learned clause is not only useful for learning/forgetting
    But it is also useful for unit-prop, because the current unit-prop
      can only resolve  the very first clause in the f : CNF V (as a list)
    thus we can hack with learning the resolvent clause at the front and do the unit prop
    and then forgetting, this gives us a better unit-prop  
*)

Definition SucceedState  {f} (st : CDCLState f) : Prop := 
  match st with
  | existT _ _ (existT _ s _) =>
    match s with
    | (_, d) :: _ => CNFByPAssignment f d = Some true
    | _ => False
    end
  end.

Definition FailedState  {f} (st : CDCLState f) : Prop := 
    match st with
    | existT _ _ (existT _ s _) =>
      match s with
      | (_, d) :: nil => CNFByPAssignment f d = Some false
      | _ => False
      end
    end.


Definition FinalState_Dec:
  forall {f} (st : CDCLState f),
    {SucceedState st} + {FailedState st} + {~ (SucceedState st) /\ ~ (FailedState st)}.
Admitted.


(* The invariant here for (k : CDCLState f)
  1. if SucceedState k  
      then assignment from k can evaluate f into true
  2. if FailedState k
      then I can extract (RProof (CNFFormula f) fbot)
*)



(* The following are the extracted functions 
    they all have similar signature as 
    CDCL f * (... sth else needed) -> CDCL f
    basically these can be seen as 
    non-determinstic transition in a (CDCL f) world
*)

(* One step unit-prop spec*)

(* UnitProp until cannot spec*)

(* Guess One Literal spec*)

(* Check Success spec*)

(* Check Failure spec*)

(* Back Jump spec*)


(* Now we need to really model
    all possible (non-deterministic) transition
      inside (CDCL f) world
    using 
      the above 5 specification functions
  and then prove the transition above will give
    some good property on termination
*)

