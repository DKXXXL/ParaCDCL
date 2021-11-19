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
  

Theorem PA_consistent_with_A':
  forall {f pa g q},
    ClauseByPAssignment f pa = Some q ->
    (forall x t, 
        PA pa x = Some t ->
        PA pa x = Some (g x)
      ) ->
      ClauseByPAssignment f pa = Some (ClauseByAssignment f g).
  intros f.
  induction f; intros pa g q h0 h1;  subst; cbn in *; subst; eauto; 
  repeat breakAssumpt1; try_injection; subst; eauto.
  pose (IHf _ _ _ heq0 h1) as E.
  try rewrite heq in *; try rewrite heq0 in *; eauto; try_injection; eauto.
  assert (LiteralByAssignment a g = b) as HeqAssert1;
  subst; try (rewrite HeqAssert1 in *; rewrite HeqAssert2 in *; auto; eauto; fail); try auto.
  unfold LiteralByPAssignment in *;
  unfold LiteralByAssignment in *;
  repeat breakAssumpt1; cbn in *; try_injection; auto. 
  + pose (h1 _ _ heq) as h11; try rewrite heq in *; eauto; try_injection; subst; eauto.
  + pose (h1 _ _ heq2) as h11; try rewrite heq2 in *; eauto; try_injection; subst; eauto.
Qed. 

Theorem PA_consistent_with_A0:
  forall {f pa g q},
    CNFByPAssignment f pa = Some q ->
    (forall x t, 
        PA pa x = Some t ->
        PA pa x = Some (g x)
      ) ->
      CNFByPAssignment f pa = Some (CNFByAssignment f g).
  intros f. 
  induction f; intros pa g q h0 h1; cbn in *; subst; eauto.
  repeat breakAssumpt1; try_injection; subst; eauto.
  erewrite PA_consistent_with_A' in heq; eauto; try_injection; subst; eauto.
  pose (IHf _ _ _ heq0 h1) as heqhf; rewrite heq0 in heqhf; try_injection;subst; eauto.
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
  rewrite H3 in *; try_injection; eauto.
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
        | (_, d) :: _ => CNFByPAssignment f d = Some false
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
  
destruct (CNFByPAssignment f d); try_both_side.
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
  repeat breakAssumpt1. injection h0; intros; subst; eauto.
  destruct b; destruct b0; subst; eauto; cbn in *; try contradiction; try discriminate; eauto.
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
  (f : forall {L}, {s1 & AS L s1} -> {s2 & AS L s2}): forall {F L}, CDCLState F L -> CDCLState F L.
  intros F L st.
  destruct st as [s1 [as1 other]].
  destruct (f _ (existT _ s1 as1)) as [s2 as2].
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






(* Theorem vanilla_propagate_all_unit_clause:
  forall (C : CNF V) {trail},
  AS C trail ->
  {trail2 & 
    AS C trail2 *
    { h : trail2 <> nil |
    NoUnitClause C trail2 h}}. *)


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


Lemma FailedSt_ConflictSt {f l} (st : CDCLState f l):
    FailedState st ->
    ConflictingState st.
  intros.
  destruct st as [atrail [hf1 hf2]].
  destruct atrail as [_ | [g d] t]; subst; eauto; try contradiction; try discriminate;
  try (inversion hf1; fail); cbn in *.
  repeat breakAssumpt2. auto.
Qed.

Lemma vanilla_propagate_all_unit_clause_onestep:
  forall {f l} (st : CDCLState f l), CountUnitClausesIn st <> 0 /\ ~FailedState st ->
  {st2 : CDCLState f l | deducedLitNum st2 > deducedLitNum st /\ ~FailedState st2}
  + {st2 : CDCLState f l | ConflictingState st2}.
Admitted.



(* TODO Prove the termination of unit propagation *)
Theorem vanilla_propagate_all_unit_clause
    (fuel : nat): forall {f l} (st : CDCLState f l),
    {st2 : CDCLState f l | NoUnitClause st2 /\ ~FailedState st2}
    + {st2 : CDCLState f l | ConflictingState st2}
    + {st2 : CDCLState f l | deducedLitNum st2 > deducedLitNum st /\  ~ FailedState st2 }.
  induction fuel.
  + intros f l st.
    (* When fuel used up *)
    destruct (FailedState_Dec st) as [hfail | hnfail].
    ++ left. right. exists st; apply FailedSt_ConflictSt. auto.
    ++ destruct (CountUnitClausesIn st) eqn:hucn.
       assert (NoUnitClause st) as HNUC; [try (eapply NoUnitClause_computable; eauto; fail) | idtac].
       left. left. exists st. split; [apply HNUC | apply hnfail].
       assert (CountUnitClausesIn st <> 0) as hucn0; [try lia | idtac].
       destruct (vanilla_propagate_all_unit_clause_onestep st) as [[st2 [h1 h2]] | [st2 h1]].
       split; auto. 
       right. exists st2. auto.
       left. right. exists st2. auto.
  + (* When fuel has left*)
    intros f l st.
    (* Still check if failed *)
    destruct (FailedState_Dec st) as [hfail | hnfail].
    ++ left. right. exists st; apply FailedSt_ConflictSt. apply hfail.
    ++ destruct (CountUnitClausesIn st) eqn:hucn.
    +++
       (* No Unit Clause! We are done *)
       assert (NoUnitClause st) as HNUC; [try (eapply NoUnitClause_computable; eauto; fail) | idtac].
       left. left. exists st. split; [apply HNUC | apply hnfail].
    +++  
       (* Still Unit Clause...  *)
       assert (CountUnitClausesIn st <> 0) as hucn0; [try lia | idtac].
    (* We progress one step and see if the result is good *)
      destruct (vanilla_propagate_all_unit_clause_onestep st) as [[st2 [h1 h2]] | [st2 h1]].
      split; auto.
      ++++
        destruct (IHfuel _ _ st2) as [[[st3 hrec] | [st3 hrec]] | [st3 hrec]].
        +++++ left. left. exists st3. auto.
        +++++ left. right. exists st3. auto.
        +++++ destruct (FailedState_Dec st3) as [fail0 | nfail0]. 
          ++++++    pose (FailedSt_ConflictSt _ fail0) as fc0.
                left. right. exists st3. auto.
          ++++++      right.  exists st3. split; auto; try lia.
      ++++ left. right. exists st2. apply h1.
    (* NOT Failure yet, check if it has any more unit clause*)

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

Theorem guess_new_literal_then_maybe_conflict {f l} (st: CDCLState f l):
  {l2 & {st2 : CDCLState f l2 | deducedLitNum st2 > deducedLitNum st \/ length l2 > length l}}.
Admitted.

Definition vanilla_conflicting_analysis:
  forall {f l} (h : f <> nil) {st : CDCLState f l} 
    (H0 :ConflictingState st),
    {l2 & RProof (CNFFormula (l ++ f)) (CNFFormula l2)}.
  unfold ConflictingState.
  intros. destruct st as [s [h1 h2]].
  destruct s as [_ | [g d] t]; try contradiction.
  destruct f as [ _ | fh ft] eqn: heqf; try contradiction.
  rewrite <- heqf in H0.
  destruct (find_false_clause heqf H0) as [i [H1 H2]].
  eexists.
Admitted.
  (*
change_goal:
  forall  {g} {s} (f : CNF V),
    AssignmentStack g s ->
    RProof (CNFFormula f) (CNFFormula g) ->
    AssignmentStack f s.
*)


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


(* Use to fuel *)
Definition CountLiteral (c : CNF V) :=
  fold_right Nat.add 0 (map (fun (l: Clause V) => length l) c).
  

(* One loop of Vanilla CDCL 
    Which is basically DPLL anyway
*)
Definition VanillaCDCLOneStep {f l: CNF V} (st : CDCLState f l) (h : f <> nil) (suggest_fuel : nat):
{g | CNFByPAssignment f g =  Some true} 
+ RProof (CNFFormula f) fbot
+ {l2 & {st2 : CDCLState f l2 | (length l2 > length l \/ deducedLitNum st2 > deducedLitNum st) /\ ~ FinalState st2}}. (* Progress on Learned! *)

destruct (FinalState_Dec2 st h) as [Hfinal | H3].
+ left. auto.
+ 
 (* Main function starts here  *)
 (* First Do All the Unit Propagation *)
    destruct (vanilla_propagate_all_unit_clause suggest_fuel st) as [[[st2 [hnuc hnfail]] | [st2 hcflict]] | [st2 [hprog hnfail]]].
    ++  (* If no conflict, and successfully propagate all *)
      (* check fully assigned or not *)
      destruct (SucceedState_Dec st2).
        (* if it is fully assigned, then success extract*)
        +++ left. left. eapply (SucceedSt_extract st2); auto. 
        (* If it is guess a literal and progress, we know no conflict will happen  *)
        +++ destruct ()
          
        left. left. exists l. exists st2. unfold FinalState. intro FS; destruct FS; try contradiction.
    
    (* If conflict happens *)
    ++ destruct (FailedState_Dec st2).
      (* check if failure state *)
          (* if failure, uses failure extract *)
          +++ right. eapply (FailedSt_extract st2); auto.  
          (* if not *)
          +++ 
            (* Do conflict analysis to get a new learned clause *)
            left. left. 
            destruct (vanilla_conflicting_analysis h  hcflict) as [l2 hl2].
            destruct (learn_CS_spec1 hl2 st2) as [hst2 hst2info].
            exists (l2 ++ l). exists hst2. intro hF.
            unfold FinalState in *; unfold ConflictingState in *; cbn in *.
            destruct st2 as [st21 st22]; 
            destruct hst2 as [hst21 hst22]; cbn in *;
            repeat breakAssumpt2.
            inversion hst2info; intros; subst; eauto.
            try rewrite hcflict in hF. destruct hF; try discriminate; try contradiction.
            (* Do trivial back track *)
    (* not completely propagated *)
    ++ 
            Admitted.



         




(* The main Procedure to be extract *)
Definition VanillaCDCLAlg {f l: CNF V} (st : CDCLState f l) (h : f <> nil) (fuel : nat) :
  {l2 & {st2 : CDCLState f l2 | (length l2 > length l \/ deducedLitNum st2 > deducedLitNum st) /\ ~ FinalState st2}} 
  (* Fail to achieve the final result, just returning the intermediate state, but will have progress info *)
  + {g | CNFByPAssignment f g = Some true} 
  + RProof (CNFFormula f) fbot.
Admitted.


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