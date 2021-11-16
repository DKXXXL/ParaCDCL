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

Print succeed_AS_spec.






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


Axiom rp_cnf_weaken: forall {g f},
  RProof (CNFFormula (g ++ f)) (CNFFormula f).

Axiom rp_cnf_conj: forall {f g h},
  RProof (CNFFormula f) (CNFFormula g) ->
  RProof (CNFFormula f) (CNFFormula h) ->
  RProof (CNFFormula f) (CNFFormula (g ++ h)).

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

Definition SucceedState_Dec {f l} (st : CDCLState f l):
  {SucceedState st} + {~SucceedState st}.
Admitted.

Definition FailedState_Dec {f l} (st : CDCLState f l):
  {FailedState st} + {~FailedState st}.
Admitted.

Definition FinalState_Dec:
  forall {f l} (st : CDCLState f l),
    {SucceedState st} + {FailedState st} + {~ FinalState st}.
Admitted.



Definition ConflictingState_Dec:
  forall {f l} (st : CDCLState f l),
    {ConflictingState st} + {~ ConflictingState st}.
Admitted.




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

Axiom rp_cnf_weaken3: forall {index f},
  index < length f ->
  RProof (CNFFormula f) (ClauseFormula (nth index f nil)).

Axiom rp_contra0: forall {C},
  RProof (fconj C (fneg C)) fbot.

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
Qed.

Definition nthsafe {T} (i : nat) (l : list T) (h : i < length l) : T.
  destruct (nth_error l i) eqn:heq0.
  + exact t.
  + pose (nth_error_overbound heq0); lia.
Qed.


Definition UnitClause (c : Clause V) a :=
  {i & { h : i < length c |
       LiteralByPAssignment (nthsafe i c h) a = None
       /\ forall j (h2 : j < length c), 
            j <> i -> 
            LiteralByPAssignment (nthsafe j c h2) a = Some false
  }}.

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

Definition UnitClause_Dec:
  forall (c : Clause V) a,
    UnitClause c a + {UnitClause c a -> False}.
Admitted.

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
Admitted.

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
      forall i (h : i < length f), UnitClause (nthsafe i f h) d -> False).
  Defined.



(* Theorem vanilla_propagate_all_unit_clause:
  forall (C : CNF V) {trail},
  AS C trail ->
  {trail2 & 
    AS C trail2 *
    { h : trail2 <> nil |
    NoUnitClause C trail2 h}}. *)
  
Theorem vanilla_propagate_all_unit_clause:
    forall {f l} (st : CDCLState f l),
    {st2 : CDCLState f l | NoUnitClause st2 /\ ~FailedState st2}
    + {st2 : CDCLState f l | ConflictingState st2}.
Admitted.


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
Qed.
  

(* One loop of Vanilla CDCL 
    Which is basically DPLL anyway
*)
Definition VanillaCDCLOneStep {f l: CNF V} (st : CDCLState f l) (h : f <> nil):
{l2 & {st2 : CDCLState f l2 | ~ FinalState st2}} 
+ {g | CNFByPAssignment f g =  Some true} 
+ RProof (CNFFormula f) fbot.

destruct (FinalState_Dec st) as [[H1 | H2] | H3].
+ left. right. eapply SucceedSt_extract; auto. exact H1.
+ right. eapply  FailedSt_extract; auto. exact H2.
+ 
 (* Main function starts here  *)
 (* First Do All the Unit Propagation *)
    destruct (vanilla_propagate_all_unit_clause st) as [[st2 [hnuc hnfail]] | [st2 hcflict]].
    ++  (* If no conflict *)
      (* check fully assigned or not *)
      destruct (SucceedState_Dec st2).
        (* if it is fully assigned, then success extract*)
        +++ left. right. eapply (SucceedSt_extract st2); auto. 
        (* If it is not return this  *)
        +++ left. left. exists l. exists st2. unfold FinalState. intro FS; destruct FS; try contradiction.
    
    (* If conflict happens *)
    ++ destruct (FailedState_Dec st2).
      (* check if failure state *)
          (* if failure, uses failure extract *)
          +++ right. eapply (FailedSt_extract st2); auto.  
          (* if not *)
          +++ 
            (* Do conflict analysis to get a new learned clause *)
            (* Do trivial back track *)
            left. left. 
            destruct (vanilla_conflicting_analysis h  hcflict) as [l2 hl2].
            pose (learn_CS_spec0 hl2 st2) as hst2.
            exists (l2 ++ l). exists hst2.  admit.


         




(* The main Procedure to be extract *)
Definition VanillaCDCLAlg {f l: CNF V} (st : CDCLState f l) (h : f <> nil) (fuel : nat) :
  {l2 & {st2 : CDCLState f l2 | ~ FinalState st2}} 
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