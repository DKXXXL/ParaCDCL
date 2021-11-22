(* This file formalizes (Waldmann 2017) which does a good job
    on constructing a transition system on CDCL algorithm.
  http://rg1-teaching.mpi-inf.mpg.de/autrea-ws17/script.pdf, P29

*)
Require Import src.rproof.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

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

Ltac breakAssumpt1:=
  match goal with
  | [h0 : match ?exp with _ => _ end = _ |- _ ] => 
    let heq := fresh "heq" in
    destruct exp eqn:heq; try discriminate; try contradiction
  end.
Ltac try_injection :=
    match goal with
    | [h : Some _ = Some _ |- _] =>
      injection h; intros; subst; eauto;  generalize h; clear h;
      try_injection;
      intro h
    | _ => idtac
    end.
  

Theorem PA_consistent_with_A'':
forall {f pa g q},
  LiteralByPAssignment f pa = Some q ->
  (forall x t, 
      PA pa x = Some t ->
      PA pa x = Some (g x)
    ) ->
    LiteralByPAssignment f pa = Some (LiteralByAssignment f g).
  unfold LiteralByAssignment. unfold LiteralByPAssignment.
  intros f pa g q H0 h. repeat breakAssumpt3; cbn in *; try_injection; subst; eauto.
  erewrite h in heq0; eauto; try_injection .
Qed.

Theorem PA_consistent_with_A''':
forall {f pa g q},
  LiteralByPAssignment f pa = Some q ->
  (forall x t, 
      PA pa x = Some t ->
      PA pa x = Some (g x)
    ) ->
    LiteralByAssignment f g = q.
intros f pa g q H0 H1. erewrite PA_consistent_with_A'' in H0; eauto; try_injection; auto.
Qed.

Theorem PA_consistent_with_A':
  forall {f pa g q},
    ClauseByPAssignment f pa = Some q ->
    (forall x t, 
        PA pa x = Some t ->
        PA pa x = Some (g x)
      ) ->
      (ClauseByAssignment f g) = q.
  intros f.
  induction f; intros pa g q h0 h1;  subst; cbn in *; subst; eauto; 
  repeat breakAssumpt1; try_injection; subst; eauto; cbn in *.

  
  repeat erewrite PA_consistent_with_A'''; eauto;
  repeat try_injection; cbn in *; auto.

  repeat erewrite PA_consistent_with_A'''; eauto;
  repeat try_injection; cbn in *; auto.

  Ltac try_injection2 :=
    match goal with
    | [h : Some _ = Some _ |- _] =>
      injection h; intros; subst; eauto;  
      clear h;
      try_injection
    | _ => idtac
    end.

  try_injection2;subst; eauto;
  repeat erewrite IHf; eauto;
  repeat erewrite PA_consistent_with_A'''; eauto;
  repeat try_injection; cbn in *; auto.

  try_injection2. erewrite IHf; eauto. simpl_bool. auto.
Qed.


Theorem PA_consistent_with_A0:
  forall {f pa g q},
    CNFByPAssignment f pa = Some q ->
    (forall x t, 
        PA pa x = Some t ->
        PA pa x = Some (g x)
      ) ->
      (CNFByAssignment f g) = q.
  intros f. 
  induction f; intros pa g q h0 h1; cbn in *; subst; eauto; try_injection2; auto .
  repeat breakAssumpt1; try_injection2; subst; eauto;
  try (
    repeat erewrite PA_consistent_with_A'; eauto; cbn in *; auto;
    repeat erewrite IHf; eauto; cbn in *; simpl_bool; eauto; fail
  ).
  cbn in *.

  erewrite IHf; eauto; simpl_bool; auto.
Qed.

Theorem PA_consistent_with_A:
  forall {f pa g},
    CNFByPAssignment f pa <> None ->
    (forall x, 
        PA pa x <> None ->
        PA pa x = Some (g x)
      ) ->
      CNFByPAssignment f pa = Some (CNFByAssignment f g).

  intros f pa g H0 H1.
  assert (forall x t, 
    PA pa x = Some t ->
    PA pa x = Some (g x)) as H2.
  + intros x t h. eapply H1; subst; rewrite h in *; eauto.
    try discriminate.
  + 
  destruct (CNFByPAssignment f pa) eqn:H3;
  try (try rewrite H3 in H0; try discriminate; try contradiction; fail).
  pose (PA_consistent_with_A0 H3 H2) as res; eauto.
  rewrite res in *; try_injection; eauto.
Qed.
  

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


(* Make higher order assignment into 
    First order data.
*)
(* Definition allfalse: Assignment V := fun _ => false.
Definition newAssignment   {V : Set} `{EqDec_eq V} v b f : (Assignment V) :=
  fun k =>
    match (eq_dec k v) with
    | left _ => b
    | right _ => f k
    end.
Inductive TruthTable : (Assignment V) -> Set :=
| empty_tb : TruthTable allfalse
| assign_fa : forall {f} (v : V) (b : bool), 
  TruthTable f -> 
  TruthTable (newAssignment v b f). *)


(* Definition succeed_AS_spec: forall {f g d s},
  AS f ((g, d) ::s) ->
  CNFByPAssignment f d = Some true ->
  {g2 | CNFByAssignment f g2 = true}.
intros f g d s H0 H1. exists (extendPA d).
assert (CNFByPAssignment f d <> None) as H2. repeat rewrite H1 in *.
intro; try discriminate; try contradiction.
pose (PA_consistent_with_ExtendedA H2) as H3.
rewrite H3 in H1. inversion H1; subst; eauto.
Qed. *)

Definition succeed_AS_spec: forall {f g d s},
  AS f ((g, d) ::s) ->
  CNFByPAssignment f d = Some true ->
  {g2  | CNFByPAssignment f g2 = Some true}.
intros f g d s H0 H1. 
exists d; eauto.
Qed.







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




Definition CDCLState  (f learned: CNF V)  :=  
  {s & (AS (learned ++ f) s) * RProof (CNFFormula f) (CNFFormula learned)}.

Lemma all_clause_are_derivable: forall {f l},
  CDCLState f l ->
  RProof (CNFFormula f) (CNFFormula (l ++ f)).

  intros f l h.
  destruct h as [st [h1 h2]].
  eapply rp_cnf_conj; eauto.
Qed.

(* This learned clause is not only useful for learning/forgetting
    But it is also useful for unit-prop, because the current unit-prop
      can only resolve  the very first clause in the f : CNF V (as a list)
    thus we can hack with learning the resolvent clause at the front and do the unit prop
    and then forgetting, this gives us a better unit-prop  
*)

Definition SucceedState  {f l} (st : CDCLState f l) : Prop := 
  match st with
  | existT _ s _ =>
    match s with
    | (_, d) :: _ => CNFByPAssignment f d = Some true
    | _ => False
    end
  end.

Definition FailedState  {f l} (st : CDCLState f l) : Prop := 
    match st with
    | existT _ s _ =>
      match s with
      | (_, d) :: nil => CNFByPAssignment f d = Some false
      | _ => False
      end
    end.


Definition ConflictingState  {f l} (st : CDCLState f l) : Prop := 
      match st with
      | existT _ s _ =>
        match s with
        | (_, d) :: _ => CNFByPAssignment (l ++ f) d = Some false
        | _ => False
        end
      end.

Definition FinalState {f l} (st : CDCLState f l) :=
  SucceedState st \/ FailedState st.

Ltac try_both_side:=
  try (left; eauto; try contradiction; try discriminate; fail);
  try (right; eauto; try contradiction; try discriminate; fail).

Definition SucceedState_Dec {f l} (st : CDCLState f l):
  {SucceedState st} + {~SucceedState st}.
destruct st as [st1 st2]. cbn in *.
destruct st1 as [_ | [g d] t];try_both_side.
destruct (CNFByPAssignment f d); try_both_side.
destruct b; try_both_side.
Qed.

Definition FailedState_Dec {f l} (st : CDCLState f l):
  {FailedState st} + {~FailedState st}.
destruct st as [st1 st2]. cbn in *.
destruct st1 as [_ | [g d] t];try_both_side.
destruct t; try_both_side.
destruct (CNFByPAssignment f d); try_both_side.
destruct b; try_both_side.
Qed.


Ltac try_all_branch :=
  match goal with
  | [|- _ + {_}] =>
    try (left;try_all_branch; eauto; try contradiction; try discriminate; fail);
    try (right;try_all_branch; eauto; try contradiction; try discriminate; fail)

  |  [|- {_} + {_}] => 
    try (left;try_all_branch; eauto; try contradiction; try discriminate; fail);
    try (right;try_all_branch; eauto; try contradiction; try discriminate; fail)
  | _ => idtac
  end.


Definition FinalState_Dec:
  forall {f l} (st : CDCLState f l),
    {SucceedState st} + {FailedState st} + {~ FinalState st}.
intros. unfold FinalState.
destruct (SucceedState_Dec st); try_all_branch.
destruct (FailedState_Dec st); try_all_branch.
right. intro H0. destruct H0; try contradiction.
Qed.


Definition ConflictingState_Dec:
  forall {f l} (st : CDCLState f l),
    {ConflictingState st} + {~ ConflictingState st}.
destruct st as [st1 st2]. cbn in *.
destruct st1 as [_ | [g d] t];try_both_side.
  
destruct (CNFByPAssignment (l ++ f) d); try_both_side.
destruct b; try_both_side.
Qed.





Theorem SucceedSt_extract:
  forall {f l} (st : CDCLState f l), 
    SucceedState st ->
    {g2 | CNFByPAssignment f g2 = Some true}.

  unfold SucceedState. intros.
  destruct st as [s  other].
  destruct s; cbn in *; try contradiction. 
  destruct p. eauto.
Qed.

Theorem find_false_clause':
  forall {f : CNF V} {a h t},
    f = h :: t ->
    CNFByPAssignment f a = Some false ->
    {ClauseByPAssignment h a = Some false} +
    {CNFByPAssignment t a = Some false}.
  intros f. induction f; intros assign h t h0 h1; try contradiction; try discriminate.
  cbn in *.
  repeat breakAssumpt1; injection h0; intros; subst; eauto.
  try (destruct b0;  subst; eauto; cbn in *; try contradiction; try discriminate; eauto; fail).
  
Qed.


Theorem find_false_clause:
  forall {f : CNF V} {a h t},
    f = h :: t ->
    CNFByPAssignment f a = Some false ->
    {i | ClauseByPAssignment (nth i f nil) a = Some false /\ i < length f}.
    intros f. induction f;intros assign h t h0 h1; try contradiction; try discriminate.
    injection h0; intros; subst; eauto.
    destruct (find_false_clause' h0 h1).
    + exists 0; cbn in *; split; eauto. lia.
    + destruct t; try (cbn in *; try contradiction; try discriminate; fail).
      destruct (IHf _ _ _ eq_refl e) as [i' [hi1 hi2]].
      exists (S i'); cbn in *; split; eauto. lia.
Qed.



Theorem FailedSt_extract:
  forall {f l} (st : CDCLState f l), 
  f <> nil ->
  FailedState st ->
  RProof (CNFFormula f) fbot.

  unfold FailedState. intros.  pose st as org_st.
  destruct f; try contradiction.
  destruct st as [s other].
  destruct s; try contradiction.
  destruct p as [other2 d].
  destruct s; try contradiction.
  destruct (find_false_clause eq_refl H1)
    as [index [h1 h2]].
  pose (rp_cnf_weaken3 h2) as r.
  pose (rp_byassign2 h1) as r0.
  eapply rp_trans; [idtac | eapply rp_contra0].
  eapply rp_rconj; [eauto | idtac ].
  eapply rp_trans; [idtac | eapply r0].
  eapply rp_trans; [eapply (all_clause_are_derivable org_st) |idtac].
  destruct other as [theAS r00].
  assert (other2 = ∅); [eapply AS_no_guessing; eauto | idtac]; subst.
  pose (AssignmentStackHasRProof theAS) as res. cbn in res.
  eapply rp_trans;[idtac| exact res]; eauto.
Qed.

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



Definition lift_AS_op  
  (f : forall {L s1}, AS L s1 -> {s2 & AS L s2}): forall {F L}, CDCLState F L -> CDCLState F L.
  intros F L st.
  destruct st as [s1 [as1 other]].
  destruct (f _ _ as1) as [s2 as2].
  exact  (existT _ s2 (as2, other)).
Qed.

(* One step unit-prop spec*)



Lemma nth_error_overbound:
  forall {T}  {l : list T} {i}
    (H0: nth_error l i = None),
    i >= length l.
  intros T l. induction l; intros; cbn in *; subst;  eauto.
  lia. destruct i; subst; try contradiction; try discriminate.
  cbn in *. pose (IHl _ H0). lia.
Defined.

(* Definition nthsafe {T} (i : nat) (l : list T) (h : i < length l) : T.
  destruct (nth_error l i) eqn:heq0.
  + exact t.
  + pose (nth_error_overbound heq0); lia.
Defined. *)



Definition UnitClause (c : Clause V) a :=
  {i & { h : i < length c |
       LiteralByPAssignment (nthsafe i c h) a = None
       /\ forall j (h2 : j < length c), 
            j <> i -> 
            LiteralByPAssignment (nthsafe j c h2) a = Some false
  }}.

Lemma UnitClauseNeverEmpty c :
  forall {a}, UnitClause c a ->
  c <> nil.
intros a h. 
destruct c; try (intro; eauto; try discriminate).
destruct h as [i [h _]]; cbn in *; try contradiction. lia.
Qed. 
  
Lemma UnitClauseNeverEmpty' :
  forall {a}, UnitClause nil a ->
  False.
intros a h. 
destruct h as [i [h _]]; cbn in *; try contradiction. lia.
Qed. 

(* Definition AllFalseClause (c : Clause V) a :=
  forall j (h2 : j < length c), 
    LiteralByPAssignment (nthsafe j c h2) a = Some false *)


Definition isSomefalse k := 
  match k with
  | Some false => true
  | _ => false
  end.
  
Definition isNone {A : Type} (k : option A) := 
    match k with
    | None => true
    | _ => false
  end.



Theorem find_index {A:Type} (f : A -> bool) (l : list A) :
  {i : nat | {h : i < length l |  f(nthsafe i l h) = true}} 
  + {forall i (h : i < length l), f(nthsafe i l h) = false}.
  induction l.
  + right. intros. cbn in *. lia. 
  + destruct IHl as [[i [h hindex]] | hfail].
    ++ left.  exists (S i). assert (S i < length (a :: l)) as hlt; try (cbn in *; try lia; fail). 
    exists hlt. cbn in hlt. erewrite nthsafe_red. eauto.
    ++ destruct (f a) eqn:hfa.
        +++ left. exists 0. cbn in *. eexists; eauto. lia.
        +++ right. intros i h2. destruct i; try (cbn in *; eauto; fail).
Qed.    





(* We postulate the following axio m for computation, which makes things easier
   TODO: prove it
*)
Axiom UnitClauseComputable0:
  forall {c i} a (h : i < length c),
  (
  (LiteralByPAssignment (nthsafe i c h) a) = None
  /\ forall j (h2 : j < length c), 
      j <> i -> 
      LiteralByPAssignment (nthsafe j c h2) a = Some false) ->
  (
  (LiteralByPAssignment (nthsafe i c h) a) = None
  /\ length (filter (fun x => isSomefalse (LiteralByPAssignment x a)) c) = (length c) - 1
  /\ c <> nil
  ).

Axiom UnitClauseComputable1:
  forall {c i} a (h : i < length c),
  (
  (LiteralByPAssignment (nthsafe i c h) a) = None
  /\ length (filter (fun x => isSomefalse (LiteralByPAssignment x a)) c) = (length c) - 1
  /\ c <> nil
  ) ->
  (
  (LiteralByPAssignment (nthsafe i c h) a) = None
  /\ forall j (h2 : j < length c), 
      j <> i -> 
      LiteralByPAssignment (nthsafe j c h2) a = Some false)
  .

Lemma UnitClause_computable_chara:
  forall {c a},
    UnitClause c a ->
    {i & { h : i < length c | (
  (LiteralByPAssignment (nthsafe i c h) a) = None
  /\ length (filter (fun x => isSomefalse (LiteralByPAssignment x a)) c) = (length c) - 1
  /\ c <> nil
  )} }.
  intros c a h.
  destruct h as [index [h0 [h01 h02]]].
  exists index. exists h0.
  eapply UnitClauseComputable0; eauto.
Qed.


Theorem UnitClause_Dec:
  forall (c : Clause V) a,
  UnitClause c a + {UnitClause c a -> False}.

destruct c eqn:heqc;[right; eapply UnitClauseNeverEmpty'; eauto | idtac].
assert (c <> nil); [try intro; subst; try contradiction; try discriminate | idtac].
intros a. 
destruct (find_index (fun x => isNone (LiteralByPAssignment x a)) c) as [[i [h hf]] | hk]; unfold isSomefalse in *;
try (right; intro HC; destruct (UnitClause_computable_chara HC) as [index [h1 [h11 [h12 h13]]]]; subst; try contradiction; fail).
+
  repeat breakAssumpt1.
  destruct (eq_dec 
    (length (filter (fun x => isSomefalse (LiteralByPAssignment x a)) c))
    ((length c) - 1)
  ); try (right; intro HC; destruct (UnitClause_computable_chara HC) as [index [h1 [h11 [h12 h13]]]]; subst; try contradiction; fail).
  left. exists i. subst.  exists h. unfold isNone in hf. repeat breakAssumpt1.
      split; eauto.
      eapply (UnitClauseComputable1 a h). split; eauto.
+ right. intro HC. destruct HC as [index [h2 [h21 h22]]].
  subst. clean_pose (hk index h2). 
  unfold isNone in *. repeat breakAssumpt1.
Qed.
(* 
Theorem partition (f : A -> bool) (l : list A):
  {l1 : list {i : nat & {h : i < length l | f (nthsafe ) }} & 
    
  } 
*)




(* Search ({_ < _} + {_}). *)



Definition UnitClause_UnitLiteral {c a} (u : UnitClause c a) : Literal V.
  destruct u as [i [h hh]].
  exact (nthsafe i c h).
Defined.


Theorem UnitClauseLiteral_None {c a x b} (u : UnitClause c a):
  UnitClause_UnitLiteral u = ToLiteral x b ->
  PA a x = None.
  unfold UnitClause_UnitLiteral.
  intros H0. destruct u as [i [h [h1 h2]]]. 
  destruct b; cbn in *; rewrite H0 in *; cbn in *; eauto.
  repeat breakAssumpt1; eauto.
Qed.


(* 
  unit_prop_AS_spec:
  forall  {l c g d s f x b},

    AS ((l::c)::f) ((g,d) :: s) -> 
    l = ToLiteral x b ->
    (* eval C under d = false -> *)
    ClauseByPAssignment c d = Some false ->
    (* PA d l = None -> *)
    forall (h : PA d x = None),
    AS ((l::c)::f) ((g,d[x := b]h) :: s).
*)


Theorem UnitClause_AS_spec:
  forall  {c f g d s x b} (u : UnitClause c d),
    AS (c::f) ((g,d) :: s) -> 
    UnitClause_UnitLiteral u = ToLiteral x b ->
    forall (h : PA d x = None),
    AS (c::f) ((g,d[x := b]h) :: s).
intros c f g d s x b u H0 H1 H2. eapply deduce_as; auto.
destruct u as [index [h0 [h1 h2]]]; cbn in *.
rewrite <- H1 in *.
eapply rp_trans; [idtac | eapply rp_unitprop; eauto].
assert (RProof 
          (fconj
            (fconj (ClauseFormula c)
              (CNFFormula f))
            (LiteralsFormPA g))
            (ClauseFormula c)) as Hproof2; [eauto | idtac].
eapply rp_rconj; [exact Hproof2 | idtac].
pose (AssignmentStackHasRProof H0) as hproof1. cbn in *. eauto.
Qed.

Lemma AS_no_nil:
  forall {f}, AS f nil -> False.
  intros. inversion H0.
Qed.

Definition HasUnitClause_in_st {f l} (st : CDCLState f l): Set.
(* refine (
  match st with 
  | existT _ ((_, d) :: _ ) _ =>
    
  | _ => _
  end
). *)
  destruct st as [[ | [g d] s ] [astack]].
  destruct (AS_no_nil astack).
  exact {i & {h : i < length (l ++ f) & 
  UnitClause (nthsafe i (l ++ f) h) d
}}.
Defined.



Fixpoint lenFA {T} (f : FiniteAssignment T) := 
  match f with
  | empty_fa => 0
  | assign_fa _ _ t _ => S (lenFA t)
  end.
(* Print isUnitClause. *)
Definition deducedLitNum {f l} (st : CDCLState f l) : nat.
  destruct st as [atrail [hf1 hf2]].
  destruct atrail as [_ | [g [d1 d2]] t].
  exact 0.
  exact (lenFA d2).
Defined.


Lemma ToLiteralInjective:
  forall y,
    {x & {b & y = ToLiteral x b}}.
  intro y. unfold ToLiteral. 
  destruct y as [v | v]; exists v; [
    exists true | exists false
  ]; cbn in *; auto.
Qed.

Lemma nthsafe_nthdefault:
  forall {A} {l : list A} {i h k},
    nthsafe i l h = nth i l k.
  intros A l. induction l; intros; try (cbn in *; try lia; fail).
  destruct i.
  cbn in *; auto.
  erewrite nthsafe_red. simpl. eauto.
  Unshelve. cbn in *. lia.
Qed.
  

Lemma UnitClause_AS_spec_in_st:
  forall  {f l}  (st : CDCLState f l),
    HasUnitClause_in_st st ->
    {st2 : CDCLState f l & deducedLitNum st2 > deducedLitNum st}.
  intros f l [a [astack p]] h.
  destruct a as [hnil | [g d] t];
  try (destruct (AS_no_nil astack); fail); cbn in h.
  destruct h as [i0 [hle [i1 [hle2 [huc0 huc1]]]]].
  remember (nthsafe i1 (nthsafe i0 (l ++ f) hle) hle2) as targetL.
  remember (nthsafe i0 (l ++ f) hle) as targetC.
  destruct (ToLiteralInjective targetL) as [v [b htv]].
  assert (PA d v = None) as hdnvb. 
  + unfold LiteralByPAssignment in huc0.
    unfold ToLiteral in htv.
    repeat breakAssumpt1;
    destruct b; cbn in *; try (injection htv; intros; subst; eauto; try discriminate; fail);
    try discriminate.
  + assert (AS (l ++ f) ((g, d[v:=b]hdnvb) :: t)) as nextAS.

    ++  subst. apply deduce_as;auto. try rewrite <- htv.   
        (* rewrite HeqtargetL in *. *)
        eapply rp_trans; [idtac | apply rp_unitprop; auto].
        eapply rp_rconj;[idtac | eapply AssignmentStackHasRProof; eauto].
        eapply rp_trans; [eapply rp_weaken; eauto | idtac].
        erewrite nthsafe_nthdefault; eauto.
    ++  eexists (existT _ ((g, d [v := b] hdnvb) :: t) (nextAS, p)).
        destruct d. cbn in *. lia.
Qed.
    

Theorem UnitClauseAsLiteral:
  forall  {c d} (u : UnitClause c d),
    {x & {b & UnitClause_UnitLiteral u = ToLiteral x b}}.
  intros c d [index [hle [hindex hu4]]].
  cbn in *. apply ToLiteralInjective.
Qed. 



(* Definition isUnitClause (c : Clause V) (a : PAssignment V) : bool.
  destruct (UnitClause_Dec c a).
  exact true.
  exact false.
Defined. *)


Fixpoint CountUnitClauses (f : CNF V) (assign : PAssignment V) : nat :=
  match f with
  | nil => 0
  | cons h t =>
    if (UnitClause_Dec h assign) then 1 else 0 + CountUnitClauses t assign
  end.  

Definition CountUnitClausesIn {f l} (st : CDCLState f l) : nat.
  destruct st as [atrail [hatrail hp]].
  destruct atrail as [_ | [g d] t]; try (inversion hatrail; fail).
  exact (CountUnitClauses (l ++ f) d).
Defined.

Ltac breakAssumpt2:=
  match goal with
  | [h0 : context[match ?exp with _ => _ end] |- _ ] => 
    let heq := fresh "heq" in
    destruct exp eqn:heq; try discriminate; try contradiction
  end.


Lemma CountUnitClauses0_iff_allnotunitclauseA: forall {l assign},
  CountUnitClauses l assign = 0 -> 
  (forall i (h : i < length l), UnitClause (nthsafe i l h) assign -> False).
  intros l. induction l; intros; subst; cbn in *; intros; repeat breakAssumpt2; eauto; try lia.
Qed.

Lemma CountUnitClauses0_iff_allnotunitclauseB: forall {l assign},
(forall i (h : i < length l), UnitClause (nthsafe i l h) assign -> False) ->
  CountUnitClauses l assign = 0.
  intros l. induction l; intros assign H0; subst; intros; repeat breakAssumpt2; auto; try lia.
  simpl CountUnitClauses.
  destruct (UnitClause_Dec a assign) as [u | u]; subst; auto; try contradiction; try discriminate.
  + assert False; try contradiction.
    assert (0 < length (a::l)) as hle; try (cbn in *; try lia; fail).
    apply (H0 0 hle u). 
  + apply IHl; auto. intros. 
    assert (S i < length (a::l)) as hle2; try (cbn in *; try lia; fail).
    apply (H0 (S i) hle2); auto. erewrite nthsafe_red; auto.
  exact H1.
Qed.

Definition NoUnitClause {f l}
  (st : CDCLState f l) 
  (* (atrail : list (PAssignment V * PAssignment V)) 
  (h2 : atrail <> nil)  *)
  : Prop.
  destruct st as [atrail [AT rp]].
  destruct atrail as [_ | h t]; subst; eauto; try contradiction; try discriminate.
  + inversion AT.
  + destruct h as [g d].
    exact (
      forall i (h : i < length (l ++ f)), UnitClause (nthsafe i (l ++ f) h) d -> False).
  Defined.



Theorem NoUnitClause_computable: forall {f l} {st : CDCLState f l}, 
  NoUnitClause st <-> (CountUnitClausesIn st = 0).
  split; intros; destruct st as [atrail [AT rp]];
    destruct atrail as [_ | [g d] t]; subst; eauto; try contradiction; try discriminate;
    try (inversion AT; fail); cbn in *.
  + eapply CountUnitClauses0_iff_allnotunitclauseB; auto.
  + eapply CountUnitClauses0_iff_allnotunitclauseA; auto.
Qed.

Print sumor.


Theorem HasUnitClause_Dec:
  forall {f l} (st : CDCLState f l),
    HasUnitClause_in_st st + {NoUnitClause st}.
  intros f l [a [astack p]]. 
  destruct a as [| [g d] s];
    try (destruct (AS_no_nil astack); fail).
    cbn in *.
  pose (fun x =>
    match UnitClause_Dec x d with
    | inleft _ => true
    | inright _ => false 
    end
  ) as ff.
  destruct (find_index ff (l++f)) as 
  [[index [hle h2]] | hnonfound]; cbn in *.
  + unfold ff in *. destruct (UnitClause_Dec (nthsafe index (l ++ f) hle) d); try discriminate; try contradiction.
    left. exists index. exists hle. auto.
  + right. intros index hle2 H0.
  unfold ff in hnonfound. 
  clean_pose (hnonfound index hle2).
  destruct (UnitClause_Dec (nthsafe index (l ++ f) hle2) d); try discriminate; try contradiction.
Qed.




(* Theorem FindUnitClauseOrNone: forall {f l} {st : CDCLState f l}, 
  {i & {h : i < length (l ++ f) | }} + {NoUnitClause st}. *)







(* Theorem vanilla_propagate_all_unit_clause:
  forall (C : CNF V) {trail},
  AS C trail ->
  {trail2 & 
    AS C trail2 *
    { h : trail2 <> nil |
    NoUnitClause C trail2 h}}. *)



Lemma CNFByAssignmentImplication:
  forall {l f d},
  CNFByPAssignment f d = Some false ->
  CNFByPAssignment (l ++ f) d = Some false.
  intros l. induction l; intros;
  cbn in *; try discriminate. auto.
  repeat erewrite IHl in *; eauto; cbn in *.
  breakAssumpt3; cbn in *; simpl_bool; auto.
  destruct b; auto.
  Qed.
  

Lemma FailedSt_ConflictSt {f l} (st : CDCLState f l):
    FailedState st ->
    ConflictingState st.
  intros.
  destruct st as [atrail [hf1 hf2]].
  destruct atrail as [_ | [g d] t]; subst; eauto; try contradiction; try discriminate;
  try (inversion hf1; fail); cbn in *.
  repeat breakAssumpt2.
   eapply CNFByAssignmentImplication; auto.
Qed.


Lemma nConflictSt_nFailedSt {f l} (st : CDCLState f l):
    ~ConflictingState st ->
    ~FailedState st.
  intros H0 H1. pose (FailedSt_ConflictSt _ H1); try contradiction.
Qed.



Lemma vanilla_propagate_all_unit_clause_onestep:
  forall {f l} (st : CDCLState f l), 
  CountUnitClausesIn st <> 0 /\ ~ConflictingState st ->
  {st2 : CDCLState f l | deducedLitNum st2 > deducedLitNum st /\ ~ConflictingState st2}
  + {st2 : CDCLState f l | ConflictingState st2}.

Ltac check_conflicting_state_and_return st:=
  let hfinal := fresh "hfinal"
  in let    H := fresh "H"
  in destruct (ConflictingState_Dec st) as [Hfinal | H]; [right; exists st; auto | idtac].
  
  intros f l st [h0 h1].
  destruct (HasUnitClause_Dec st) as [h2 | h2].
  + destruct (UnitClause_AS_spec_in_st _ h2) as [st2 h3].
    check_conflicting_state_and_return st2.
    left. exists st2. eauto.
  + rewrite (NoUnitClause_computable) in h2. try contradiction.
Qed.



(* TODO Prove the termination of unit propagation *)
Theorem vanilla_propagate_all_unit_clause
    (fuel : nat): forall {f l} (st : CDCLState f l),
    {st2 : CDCLState f l | deducedLitNum st2 >= deducedLitNum st /\ NoUnitClause st2 /\ ~ConflictingState st2}
    + {st2 : CDCLState f l | ConflictingState st2}
    + {st2 : CDCLState f l | deducedLitNum st2 > deducedLitNum st /\  ~ ConflictingState st2 }.
  induction fuel.
  + intros f l st.
    (* When fuel used up *)
    destruct (ConflictingState_Dec st) as [hfail | hnfail].
    ++ left. right. exists st. auto.
    ++ destruct (CountUnitClausesIn st) eqn:hucn.
       assert (NoUnitClause st) as HNUC; [try (eapply NoUnitClause_computable; eauto; fail) | idtac].
       left. left. exists st. repeat split; [try auto | try apply HNUC | try apply hnfail].
       assert (CountUnitClausesIn st <> 0) as hucn0; [try lia | idtac].
       destruct (vanilla_propagate_all_unit_clause_onestep st) as [[st2 [h1 h2]] | [st2 h1]].
       split; auto. 
       right. exists st2. auto.
       left. right. exists st2. auto.
  + (* When fuel has left*)
    intros f l st.
    (* Still check if failed *)
    destruct (ConflictingState_Dec st) as [hfail | hnfail].
    ++ left. right. exists st. auto.
    ++ destruct (CountUnitClausesIn st) eqn:hucn.
    +++
       (* No Unit Clause! We are done *)
       assert (NoUnitClause st) as HNUC; [try (eapply NoUnitClause_computable; eauto; fail) | idtac].
       left. left. exists st. repeat split; [try auto | try apply HNUC | apply hnfail].
    +++  
       (* Still Unit Clause...  *)
       assert (CountUnitClausesIn st <> 0) as hucn0; [try lia | idtac].
    (* We progress one step and see if the result is good *)
      destruct (vanilla_propagate_all_unit_clause_onestep st) as [[st2 [h1 h2]] | [st2 h1]].
      split; auto.
      ++++
        destruct (IHfuel _ _ st2) as [[[st3 hrec] | [st3 hrec]] | [st3 hrec]].
        +++++ left. left. exists st3. destruct hrec as [hrec1 [hrec2 hrec3]]; repeat split; try auto. try lia.
        +++++ left. right. exists st3. auto.
        +++++ destruct (ConflictingState_Dec st3) as [fail0 | nfail0]. 
          ++++++  
                left. right. exists st3. auto.
          ++++++      right.  exists st3. split; auto; try lia.
      ++++ left. right. exists st2. apply h1.
    (* NOT Failure yet, check if it has any more unit clause*)

Qed.


Axiom rp_false_by_eval:
  forall f, 
    CNFByPAssignment f ∅ = Some false ->
    RProof (CNFFormula f) fbot.



Theorem vanilla_backtracking_helper t:
  forall {f} (stack : AS f t) {b g1 d1 t1},
    CNFByPAssignment f ∅ = None ->
    t = ((g1,d1)::t1) ->
    CNFByPAssignment f d1 = Some b ->
    {g2 & {d2 & {t2 & {a : AS f ((g2,d2)::t2) & CNFByPAssignment f d2 = None}}}}.
induction t.
+ intros f h. destruct (AS_no_nil h).
+ intros f stack b g1 d1 t1 H0 H1 H2. 
inversion H1; subst.
destruct t1 as [_ | [t1g t1d] t1t].
++ exists ∅. exists ∅. exists nil. exists (empty_as f). auto.
++ 
assert (AS f ((t1g, t1d) :: t1t)) as nextSearch; [eapply (AssignmentStackMonotoncity stack); eauto; try (intro; discriminate) | idtac].
destruct (CNFByPAssignment f t1d) eqn:heqcnf.  
    apply  (IHt _ nextSearch b0 _ _ _ H0 eq_refl). auto.
    exists t1g. exists t1d. exists t1t. exists nextSearch. auto.
Qed.



Definition vanilla_backtracking:
  forall {f l} (st : CDCLState f l), 
  CNFByPAssignment (l ++ f) ∅ = None ->
  ConflictingState st ->
  {st2 : CDCLState f l | ~ ConflictingState st2}.

intros f l [trail [astack p]] h0 h1.
destruct trail as [_ | [g d] t];
[try destruct (AS_no_nil astack) | idtac].
cbn in *. 
destruct (vanilla_backtracking_helper _ astack h0 eq_refl h1) as [g2 [d2 [t2 [astack2 h2]]]].
exists (existT _ ((g2, d2) :: t2) (astack2, p)).
cbn in *. rewrite h2. intro. try discriminate.
Qed.




(* UnitProp until cannot spec*)





(* Guess One Literal spec*)

(*

decide_AS_spec  {f g d s} x b 
  (stack : AS f ((g, d)::s)) 
  (h : PA d x = None) :
  AS f (((g[x := b](AssignmentStackGSubD2 stack _ h)), d[x:=b] h)::(g,d)::s).

*)

(* Check Success spec*)


(*
succeed_AS_spec: forall {f g d s},
  AS f ((g, d) ::s) ->
  CNFByPAssignment f d = Some true ->
  {g2 | CNFByAssignment f g2 = true}
*)


(* Check Failure spec*)

(*

fail_AS_spec: forall {c f g d},
  AS (c::f) ((g, d) ::nil) ->
  ClauseByPAssignment c d = Some false ->
  RProof (CNFFormula (c:: f)) fbot.

  *)

(* Back Jump spec*)

(*


backjump_AS_spec: forall  {f C k g d s l} x b,
  AS f (k ++ (g,d) :: s) -> 
  l = ToLiteral x b ->
  (* f ⊧ C ∨ l*)
  RProof (CNFFormula f) (fdisj C (flit l)) ->
  (* eval C under d = false -> *)
  FormulaByPAssignment C d = Some false ->
  (* PA d l = None -> *)
  forall (h : PA d x = None),
  AS f ((g,d[x := b]h) :: s).

*)

Definition FinalState_Dec2
  {f l} (st : CDCLState f l) (h : f <> nil):
    {g | CNFByPAssignment f g =  Some true} 
    + RProof (CNFFormula f) fbot
    + {~ FinalState st}.
intros. unfold FinalState.
destruct (SucceedState_Dec st).
+ left. left. apply (SucceedSt_extract st); auto. 
+ destruct (FailedState_Dec st).
  ++ left. right. apply (FailedSt_extract st); auto.
  ++ right. intro H0. destruct H0; try contradiction.
Qed.



Lemma not_all_assigned1  {f d} :
  CNFByPAssignment f d = None ->
  exists i, exists (h : i < length f), 
    ClauseByPAssignment (nthsafe i f h) d = None.
Admitted.

Lemma not_all_assigned2  {c d} :
  ClauseByPAssignment c d = None ->
  exists i, exists (h : i < length c), 
    LiteralByPAssignment (nthsafe i c h) d = None.
Admitted.
  



Lemma EvalOnLess:
  forall {l f d},
    CNFByPAssignment (l ++ f) d = Some true ->
    CNFByPAssignment f d = Some true.

intros l. induction l; intros; eauto; cbn in *.
repeat breakAssumpt1; cbn in *. inversion H0; subst; eauto.
Qed.


Lemma not_all_assigned3: forall {f l} (st: CDCLState f l),
~ SucceedState st /\ ~ ConflictingState st -> forall g d t q,  
st = existT _ ((g,d)::t) q ->
  
  CNFByPAssignment (l ++ f) d = None.
  unfold FinalState. 
  intros f l st [h0 h1]  g d t [astack p]  heq. subst; cbn in *.
  destruct (CNFByPAssignment (l ++ f) d) eqn: heqCNF; auto.
  destruct b; try contradiction.
  destruct (h0 (EvalOnLess heqCNF)); eauto.
Qed.
  
  
Lemma LiteralByPAssignmentNone_PANone: forall {b x l d},
  l = ToLiteral x b ->
  LiteralByPAssignment l d = None <->
  PA d x = None.
  intros b. unfold LiteralByPAssignment. 
  intros; subst;
  destruct b; cbn in *; auto. split; auto.
  split; intros; repeat breakAssumpt3; auto.
Qed.

Fixpoint negLiteralForm {V : Set} `{EqDec_eq V} {f} (fa : FiniteAssignment f) {struct fa} : Clause V :=
  match fa with
  | empty_fa => nil
  | assign_fa v b f' _ => (ToLiteral v (negb b)) :: (negLiteralForm f')
  end.

Definition negLiteralFormPA {V : Set} `{EqDec_eq V} (pa : PAssignment V) : Clause V :=
  let (f, p) := pa 
  in negLiteralForm p.


Axiom rp_cnf_false_neg:
  forall {f d},
  CNFByPAssignment f d = Some false ->
  RProof (CNFFormula f) (CNFFormula ((negLiteralFormPA d)::nil)).

  
Definition vanilla_conflicting_analysis:
  forall {f l} (h : f <> nil) {st : CDCLState f l} 
    (H0 :ConflictingState st),
    {l2 & {_: RProof (CNFFormula (l ++ f)) (CNFFormula l2) | l2 <> nil}}.
  unfold ConflictingState.
  intros. destruct st as [s [h1 h2]].
  destruct s as [_ | [g d] t]; try contradiction.
  exists (((negLiteralFormPA d)::nil)).
  eexists (rp_cnf_false_neg _); eauto. intro. try discriminate.
  Unshelve. auto.
Qed.




(* Learn New Clause *)
Definition learn_CS_spec0 {f learned g}
  (h0 : RProof (CNFFormula (learned ++ f)) (CNFFormula g))
  (h1 : CDCLState f learned):
  CDCLState f (g ++ learned).
  destruct h1 as [s1 [as1 proof1]].
  eexists. split.
    (* Constructing AS using change goal*)
    + rewrite <- List.app_assoc.
      eapply change_goal; [idtac | eapply rp_cnf_weaken]; eauto.
    (* Constructing RProof using rproof *)
    + eapply rp_cnf_conj;
      [idtac | eauto].
      eapply rp_trans;
      [idtac | eauto].
      eapply rp_cnf_conj; eauto.
Defined.

Definition learn_CS_spec1 {f learned g}
  (h0 : RProof (CNFFormula (learned ++ f)) (CNFFormula g))
  (h1 : CDCLState f learned):
  {st2 : CDCLState f (g ++ learned)
    | projT1 st2 = projT1 h1
    }.
  exists (learn_CS_spec0 h0 h1). 
  unfold learn_CS_spec0. 
  destruct h1 as [s1 p].
  destruct p as [as1 proof1]. cbn in *. auto.
Qed.




Lemma NoUnitClause_NoConflictOneMoreDeduced:
 forall {f l} (st st2: CDCLState f l) (hnnil : f <> nil), 
  NoUnitClause st ->
  ((deducedLitNum st2) = S (deducedLitNum st)) ->
  ~ConflictingState st2.
Admitted.


Theorem guess_new_literal_and_no_conflict {f l} (st: CDCLState f l) (hnnil : f <> nil)
  (h0: ~ SucceedState st /\ ~ ConflictingState st) :
  NoUnitClause st ->
  {l2 & {st2 : CDCLState f l2 | (deducedLitNum st2 > deducedLitNum st \/ length l2 > length l) /\ length l2 >= length l /\ ~ConflictingState st2}}.
  
clean_pose (not_all_assigned3 _ h0). clear h0.
destruct st as [a [astack hp]] eqn:heqst.
destruct a as [_ | [ag ad] att];[try (destruct (AS_no_nil astack); auto; fail) | idtac].
clean_pose (h _ _ _ _ eq_refl). clear h.
clean_pose (not_all_assigned1 h0). clear h0.
pose (
  fun x => 
  match (ClauseByPAssignment x ad) with
  | None => true
  | _ => false
  end
) as f1.
pose (
  fun x => 
  match (LiteralByPAssignment x ad) with
  | None => true
  | _ => false
  end
) as f2.
destruct (find_index f1 (l ++ f)) as [[index1 [hindex1 p1]] | hh].
unfold f1 in p1. repeat breakAssumpt1.
destruct (find_index f2 ((nthsafe index1 (l ++ f) hindex1))) as [[index2 [hindex2 p2]] | hh2].
unfold f2 in p2. repeat breakAssumpt1.
remember (nthsafe index2 (nthsafe index1 (l ++ f) hindex1) hindex2) as targetL.
destruct (ToLiteralInjective targetL) as [x [b hxb]].

erewrite  LiteralByPAssignmentNone_PANone in heq0; [idtac | eauto].
clean_pose (AssignmentStackGSubD2 astack _ heq0).
assert (AS (l ++ f) ((ag[x:=b]h0, ad[x:=b]heq0)::(ag, ad) :: att)) as nextStack.
eapply guess_as. apply astack.
pose ((existT _ ((ag [x := b] h0, ad [x := b] heq0) :: (ag, ad) :: att) (nextStack, hp)): CDCLState f l) as nextState.
(* destruct (vanilla_no_conflict  hnnil nextState) as [l3 [st3 [hst31 [hst32 hst33]]]]. *)
exists l. 
exists nextState.
repeat split; try lia; try auto. destruct ad; cbn in *. try lia.
eapply NoUnitClause_NoConflictOneMoreDeduced; eauto. 
destruct ad. cbn in *. auto.

+ (* Contradictions happen here *)
assert False;[idtac | try contradiction].
destruct (not_all_assigned2 heq) as [index2 [hindex2 hhindex2]].
clean_pose (hh2 index2 hindex2). unfold f2 in *. repeat breakAssumpt1.
+ assert False;[idtac | try contradiction].
destruct h as [index1 [hindex1 hhindex1]].
clean_pose (hh index1 hindex1). unfold f1 in *. repeat breakAssumpt1; auto.
Qed.


  (*
change_goal:
  forall  {g} {s} (f : CNF V),
    AssignmentStack g s ->
    RProof (CNFFormula f) (CNFFormula g) ->
    AssignmentStack f s.
*)







(* Use to fuel *)
Definition CountLiteral (c : CNF V) :=
  fold_right Nat.add 0 (map (fun (l: Clause V) => length l) c).

(* One loop of Vanilla CDCL 
    Which is basically DPLL anyway
*)
Definition VanillaCDCLOneStep {f l: CNF V} (st : CDCLState f l) (h : f <> nil) (suggest_fuel : nat):
{g | CNFByPAssignment f g =  Some true} 
+ RProof (CNFFormula f) fbot
+ {l2 & {st2 : CDCLState f l2 | (length l2 > length l \/ deducedLitNum st2 > deducedLitNum st) /\ ~ FinalState st2 /\ ~ ConflictingState st2  /\ (length l2 >= length l)}}. (* Progress on Learned! *)

Ltac check_final_state_and_return st h:=
  let hfinal := fresh "hfinal"
  in let    H := fresh "H"
  in destruct (FinalState_Dec2 st h) as [Hfinal | H]; [left; auto | idtac].

  check_final_state_and_return st h.
 (* Main function starts here  *)
 (* First Do All the Unit Propagation *)
    destruct (vanilla_propagate_all_unit_clause suggest_fuel st) as [[[st2 [hnuc [hnfail1 hnfail2]]] | [st2 hcflict]] | [st2 [hprog hnfail]]].
    + (* If no conflict, and successfully propagate all *)
      (* check fully assigned or not *)
      destruct (SucceedState_Dec st2).
        (* if it is fully assigned, then success extract*)
        ++ left. left. eapply (SucceedSt_extract st2); auto. 
        (* If it is not, 
            guess a literal and progress. 
            we know no conflict will happen, but we haven't proved it yet TODO!  *)
        ++ destruct (guess_new_literal_and_no_conflict st2) as [l3 [st3 [hprog31 [hprog32 hprog33]]]].
        unfold FinalState. auto. split; [idtac | auto]. intro HH. try contradiction. auto.
        check_final_state_and_return st3 h.
        right. exists l3. exists st3. repeat split; try auto.
          destruct hprog31; [try lia | auto].
    (* If conflict happens *)
    + destruct (FailedState_Dec st2).
      (* check if failure state *)
          (* if failure, uses failure extract *)
          ++ left. right. eapply (FailedSt_extract st2); auto.  
          (* if not *)
          ++
             (*TODO we know here it is not final for st2
                Because we can prove ConflictingState st2 -> ~ SucceedState st2.
             *)
            check_final_state_and_return st2 h.
            (* Do conflict analysis to get a new learned clause *)
            destruct (vanilla_conflicting_analysis h  hcflict) as [l2 [hl2 hl2n0]].
            destruct (learn_CS_spec1 hl2 st2) as [st3 hst3info].
            destruct (ConflictingState_Dec st3) as [hst3cflict | hst3ncflict].
            +++ 
              destruct (CNFByPAssignment ((l2 ++ l) ++ f) ∅) eqn:htrybacktrack.
              destruct b. 
              ++++ left. left. exists ∅. eapply EvalOnLess; eauto.
              ++++ left. right. eapply rp_trans;[idtac | eapply rp_false_by_eval; eauto].
                    destruct st2 as [a [b hp]].
                    eapply rp_cnf_conj;[idtac| auto].
                    eapply rp_cnf_conj;[idtac | auto].
                    eapply rp_trans; [idtac | eapply hl2].
                    eapply rp_cnf_conj; eauto.
              ++++ destruct (vanilla_backtracking st3 htrybacktrack hst3cflict) as [st4 hncflict].
            
            (*TODO we know here it is not final for st4
                Because we can make backtrack more strict --
                make it return state s.t. CNFByPAssignment f 
             *)
            check_final_state_and_return st4 h.
            right.
            exists (l2 ++ l). exists st4.
            repeat split; eauto. 
            +++++ left. rewrite app_length. destruct (eq_dec (length l2) 0) as [ll20 | ll2n0]. 
            assert (l2 = nil) as Hl2nil; [try eapply  length_zero_iff_nil; eauto | idtac]. try contradiction. lia. 
            
            +++++  rewrite app_length. lia.
            +++ 
            check_final_state_and_return st3 h.
            right. exists (l2 ++ l). exists st3.
            repeat split; eauto. 
            ++++ left. rewrite app_length. destruct (eq_dec (length l2) 0) as [ll20 | ll2n0]. 
            assert (l2 = nil) as Hl2nil; [try eapply  length_zero_iff_nil; eauto | idtac]. try contradiction. lia.
            ++++  rewrite app_length. lia.
+ check_final_state_and_return st2 h.
  right.  exists l. exists st2.
  repeat split; eauto.
Qed. 
            


(* The main Procedure to be extract *)
Fixpoint VanillaCDCLAlg  (fuel : nat) {f l: CNF V} (st : CDCLState f l) (h : f <> nil) {struct fuel}:  
{g | CNFByPAssignment f g =  Some true} 
+ RProof (CNFFormula f) fbot
+ {l2 & {st2 : CDCLState f l2 | (length l2 > length l \/ deducedLitNum st2 > deducedLitNum st) /\ ~ FinalState st2 /\ ~ ConflictingState st2  /\ (length l2 >= length l)}}. (* Progress on Learned! *)
pose (CountLiteral (f ++ l)) as total_literal.
destruct fuel eqn:heqnfuel; intros.
+ apply (VanillaCDCLOneStep st h total_literal).
+ (* Some more Fuel*) 
destruct (VanillaCDCLOneStep st h total_literal) as [hfinal | [l2 [st2 [hnfinal11 [hnfinal12 [hnfinal13 hnfinal14]]]]]].
++ left. apply hfinal.
++ destruct (VanillaCDCLAlg n _ _ st2 h) as [hfinal3 | [l3 [st3 [hnfinal31 [hnfinal32 [hnfinal33 hnfinal34]]]]]].
  +++ left. apply hfinal3.
  +++ right. exists l3. exists st3. split; auto. 
  destruct hnfinal31 as [hnfinal311 | hnfinal312];
  destruct hnfinal11 as [hnfinal111 | hnfinal112];
  try lia.
  repeat split; auto. try lia.
Qed.



(* Now we need to really model
    all possible (non-deterministic) transition
      inside (CDCL f) world
    using 
      the above 5 specification functions
  and then prove the transition above will give
    some good property on termination
*)

(*
 Full 
*)

End CDCLtransition.