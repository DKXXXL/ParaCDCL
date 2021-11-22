Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
(* Here we construct the relationship between  *)


(* Copy from 
https://www.cis.upenn.edu/~plclub/metalib/current/html/CoqEqDec.html
*)

Class EqDec_eq (A : Type) :=
  eq_dec : forall (x y : A), {x = y} + {x <> y}.

Instance EqDec_eq_of_EqDec {A: Type} `(@EqDec A eq eq_equivalence) : EqDec_eq A.
  auto.
Qed.




Inductive Literal (V : Set) : Set :=
| positive : V -> Literal V
| negative : V -> Literal V.

Arguments positive {V}.
Arguments negative {V}.



Inductive Formula (V: Set) : Set :=
| flit  : Literal V -> Formula V
| fconj : Formula V -> Formula V -> Formula V
| fdisj : Formula V -> Formula V -> Formula V
| fneg  : Formula V -> Formula V
| ftop  : Formula V
| fbot  : Formula V
.


Arguments flit {V}.
Arguments fconj {V}.
Arguments fdisj {V}.
Arguments fneg {V}.
Arguments ftop {V}.
Arguments fbot {V}.

Definition Assignment (V:Set) := V -> bool.

Definition emptyAssignment {V : Set} : (V -> option bool) := fun _ => None.

Definition addAssignment   {V : Set} `{EqDec_eq V} v b f : (V -> option bool) :=
  fun k =>
    match (eq_dec k v) with
    | left _ => Some b
    | right _ => f k
    end.



(* Make a trivial partial assignment inductively defined *)
(* So that it is a finite/inductable partial assignment *)
Inductive FiniteAssignment {V : Set} `{EqDec_eq V}: (V -> option bool) -> Set :=
  | empty_fa : FiniteAssignment emptyAssignment
  | assign_fa : forall {f} (v : V) (b : bool), 
    FiniteAssignment f -> 
    f v = None ->
    FiniteAssignment (addAssignment v b f).

Hint Constructors FiniteAssignment Formula Literal.

Definition PAssignment (V:Set) `{EqDec_eq V} := {f:V -> option bool & FiniteAssignment f}.

Definition PA {V:Set} `{EqDec_eq V} (f : PAssignment V) (v : V) := projT1 f v.


Definition empty_pa  {V: Set} `{EqDec_eq V}: PAssignment V := (existT _ emptyAssignment empty_fa).
Definition assign_pa {V: Set} `{EqDec_eq V} (v : V) (b : bool) (fp : PAssignment V) (h : PA fp v = None): PAssignment V.
  destruct fp as ( f & p ). cbn in *.
  pose (addAssignment v b f) as f'.
  exact (existT _ f' (assign_fa v b p h)).
Defined.



Notation "∅" := empty_pa.


Definition Clause (V : Set) := list (Literal V).
(* ListSet of Literals *)
Definition CNF (V: Set) := list (Clause V).
(* ListSet of CNF *)


Definition LiteralByAssignment {V : Set} (c : Literal V) (a : Assignment V) : bool :=
  match c with
  | positive k => (a k)
  | negative k => (negb (a k))
  end.

Definition LiteralByPAssignment {V : Set} `{EqDec_eq V} (c : Literal V) (a : PAssignment V) : option bool :=
  match c with
  | positive k => (PA a k)
  | negative k => match PA a k with 
                  | Some k => Some (negb k)
                  | None => None 
  end
  end.

Fixpoint ClauseByAssignment {V} (c : Clause V)  (a : Assignment V): bool :=
  match c with
  | nil => false
  | (cons h t) => orb (LiteralByAssignment h a) (ClauseByAssignment t a)
  end.
Fixpoint ClauseByPAssignment {V : Set} `{EqDec_eq V} (c : Clause V) (a : PAssignment V): option bool :=
  match c with
  | nil => Some false
  | (cons h t) =>
    match LiteralByPAssignment h a, ClauseByPAssignment t a with
    | Some b1, Some b2 => Some (orb b1 b2)
    | Some true, _ => Some true
    | _, Some true => Some true
    | _, _ => None
    end
  end.

Fixpoint CNFByAssignment {V} (c : CNF V)  (a : Assignment V): bool :=
  match c with
  | nil => true
  | (cons h t) => andb (ClauseByAssignment h a) (CNFByAssignment t a)
  end.
Fixpoint CNFByPAssignment {V : Set} `{EqDec_eq V} (c : CNF V) (a : PAssignment V): option bool :=
  match c with
  | nil => Some true
  | (cons h t) => 
    match (ClauseByPAssignment h a), (CNFByPAssignment t a) with 
    | Some b1, Some b2 => Some (andb b1 b2)
    | Some false, _ => Some false
    | _ , Some false => Some false
    | _, _ => None
    end
  end.

Fixpoint FormulaByAssignment {V} (c : Formula V)  (s : Assignment V): bool:=
  let rec c := FormulaByAssignment c s in
  match c with 
  | flit  a => LiteralByAssignment a s
  | fconj a b => andb (rec a) (rec b)
  | fdisj a b => orb (rec a) (rec b)
  | fneg  a => negb (rec a)
  | ftop    => true
  | fbot    => false
  end.
Fixpoint FormulaByPAssignment {V: Set} `{EqDec_eq V} (c : Formula V) (s : PAssignment V): option bool :=
  let rec c := FormulaByPAssignment c s in
  match c with 
  | flit  a => LiteralByPAssignment a s
  | fconj a b => 
      match (rec a), (rec b) with 
      | Some a, Some b => Some (andb a b)
      | Some false, _ => Some false
      | _, Some false => Some false
      | _, _ => None
      end
  | fdisj a b => 
      match (rec a), (rec b) with 
      | Some a, Some b => Some (orb a b)
      | Some true, _ => Some true
      | _, Some true => Some true
      | _, _ => None
      end
  | fneg  a => 
      match rec a with
      | Some a => Some (negb a)
      | _ => None 
      end
  | ftop    => Some true
  | fbot    => Some false

  end.




  Definition ToLiteral {V: Set} `{EqDec_eq V} v (b : bool) : Literal V :=
    match b with 
    | true => positive v
    | false => negative v
    end.
  
  Fixpoint LiteralsForm {V : Set} `{EqDec_eq V} {f} (fa : FiniteAssignment f) : Formula V :=
    match fa with
    | empty_fa => ftop
    | assign_fa v b f' _ => fconj (flit (ToLiteral v b)) (LiteralsForm f')
    end.
  
  Definition LiteralsFormPA {V : Set} `{EqDec_eq V} (pa : PAssignment V) : Formula V :=
    let (f, p) := pa 
    in LiteralsForm p.
  
  (* Proposition LiteralsFormWf:
    forall f (fa : FiniteAssignment f), *)
      
  Fixpoint ClauseFormula {V : Set} `{EqDec_eq V} (c : Clause V): Formula V:=
    match c with 
    | nil => fbot 
    | cons h t => fdisj (flit h) (ClauseFormula t) 
    end.
  
  Fixpoint CNFFormula {V : Set} `{EqDec_eq V} (c : CNF V): Formula V :=
    match c with 
    | nil => ftop 
    | cons h t => fconj (ClauseFormula h) (CNFFormula t) 
    end.
  
Theorem ClauseWf {V : Set} `{EqDec_eq V} (c : Clause V)  : forall a,
    ClauseByAssignment c a = FormulaByAssignment (ClauseFormula c) a.
induction c; intros; cbn in *; eauto.
repeat erewrite IHc; eauto.
Qed.
  
  (* Well-defined-ness *)
Theorem CNFFormulaWf {V : Set} `{EqDec_eq V} (cnf : CNF V) : forall   a,
  CNFByAssignment cnf a = FormulaByAssignment (CNFFormula cnf) a.
induction cnf; intros; cbn in *; try eauto.
  repeat erewrite IHcnf; repeat erewrite ClauseWf; try eauto.
Qed.



(* Example:
  (forall x, s x <> None) ->
  FormulaByPAssignment *)


(*
The real RProof we need:
1. the consequent part we always need to prove conjunction of literals
2. the antecedent part is always a CNF
3. we can use an empty conjunction of literals to indicate a bottom
4. during backjump, we need to prove N ⊧ Clause v L', this
  is equivalent as N & (¬ L') ⊧ Clause
So RProof is always a CNF => Conjunction of literals
5. during the state transition, there are a lot of places
  asking for "C is false under M",
  during the coq algorithm, we will make
*)

(* We can prove the soundness of the following
    using CDPT:
    http://adam.chlipala.net/cpdt/html/Reflection.html

    there is also other chapters about prove by reflection
*)

Fixpoint nthsafe {A} (n:nat) (l:list A) (h : n < length l) {struct l} : A.
  destruct n eqn:heqn;
    destruct l eqn:heql; cbn in *; try lia.
    exact a.
    assert (n0 < length l0) as hlt; try lia.
    exact (nthsafe _ n0 l0 hlt); auto.
Defined.

Lemma nthsafe_ntherror:
  forall {A} {l : list A} {n} h1,
    nth_error l n = Some (nthsafe n l h1).
  intros A l. induction l; intros; subst; try (cbn in *; eauto; try lia; fail).
  destruct n; cbn in *; eauto.
Qed. 

Lemma nthsafe_red:
  forall A n (a:A) l h1 h2,
  nthsafe (S n) (a :: l) h1 = nthsafe n l h2.
  intros.
  assert (nth_error  (a :: l) (S n) = nth_error l n) as HEQ; try (cbn in *; try reflexivity; fail).
  rewrite (nthsafe_ntherror h1) in HEQ.
  rewrite (nthsafe_ntherror h2) in HEQ.
  injection HEQ; auto.
Qed.


Fixpoint negLiteralForm {V : Set} `{EqDec_eq V} {f} (fa : FiniteAssignment f) {struct fa} : Clause V :=
  match fa with
  | empty_fa => nil
  | assign_fa v b f' _ => (ToLiteral v (negb b)) :: (negLiteralForm f')
  end.

Definition negLiteralFormPA {V : Set} `{EqDec_eq V} (pa : PAssignment V) : Clause V :=
  let (f, p) := pa 
  in negLiteralForm p.

Theorem negLiteralFormPA_spec:
  forall p d,
    FormulaByAssignment (fneg (LiteralsFormPA p)) d = ClauseByAssignment (negLiteralFormPA p) d.
Admitted.

Inductive RProof {V: Set} `{EqDec_eq V}: Formula V -> Formula V -> Set :=
  | rp_id : forall x, RProof x x
  | rp_trans : forall {x y z},
      RProof x y ->
      RProof y z ->
      RProof x z
  (* 
  | by_evaluate :
        eval C under M = False ->
        RProof M (neg C)
    M is all of literals
    used by Unit Propagation and Backjump
  *)
  (* | res : forall M C L,
      RProof M (fdisj C L) ->
      RProof M (fneg C) ->
      RProof M L  *)
  (* Used by Unit Propagation and backjump *)
  | rp_weaken : forall X K,
      RProof (fconj X K) X
  (* Used by Unit Propagation and backjump 
      we need to collect one clause out in unit propagation
  *)
  | rp_weaken2 : forall {X} K {Y},
      RProof X Y -> RProof (fconj K X) Y 
  | rp_weaken3 : forall {X Y} K,
      RProof X Y -> RProof (fconj K X) (fconj K Y)
  (* Used by Decide *)
  | rp_contra : forall N C,
      RProof (fconj N (fconj C (fneg C))) fbot
  | rp_trivial : forall X,
      RProof X ftop
  | rp_rconj: forall {X Y Z},
      RProof X Y ->
      RProof X Z ->
      RProof X (fconj Y Z)
  | rp_comm_conj : forall A B C,
    RProof (fconj A (fconj B C)) (fconj B (fconj A C))
  | rp_byassign1:
      forall {c d},
    ClauseByPAssignment c d = Some true ->
    RProof (LiteralsFormPA d) (ClauseFormula c)
  | rp_byassign2:
      forall {c d},
    ClauseByPAssignment c d = Some false ->
    RProof (LiteralsFormPA d) (fneg (ClauseFormula c))
  | rp_res:
      forall {X Y Z : Formula V},
    RProof X (fdisj Y Z) ->
    RProof X (fneg Z) ->
    RProof X Y
  | rp_byassign4:
      forall {c d},
    FormulaByPAssignment c d = Some false ->
    RProof (LiteralsFormPA d) (fneg c)
  | rp_comm_disj:
      forall {X Y Z : Formula V},
      RProof X (fdisj Y Z) ->
      RProof X (fdisj Z Y)
  | rp_cnf_weaken: forall  {g f : CNF V},
  RProof (CNFFormula (g ++ f)) (CNFFormula f)
  | rp_cnf_conj: forall {f g h : CNF V},
  RProof (CNFFormula f) (CNFFormula g) ->
  RProof (CNFFormula f) (CNFFormula h) ->
  RProof (CNFFormula f) (CNFFormula (g ++ h))
  | rp_cnf_weaken3: forall  {index} {f : CNF V},
  index < length f ->
  RProof (CNFFormula f) (ClauseFormula (nth index f nil))
  | rp_contra0: forall {C : Formula V},
  RProof (fconj C (fneg C)) fbot
  | rp_unitprop:
  forall (c : Clause V) i d (h : i < length c),
    (forall j (h' : j < length c), 
      j <> i ->
      LiteralByPAssignment (nthsafe j c h') d = Some false) ->
    RProof (fconj (ClauseFormula c) (LiteralsFormPA d)) (flit (nthsafe i c h))
  | rp_cnf_false_neg:
  forall {f :CNF V} {d},
    CNFByPAssignment f d = Some false ->
    RProof (CNFFormula f) (CNFFormula ((negLiteralFormPA d)::nil)).




Definition rproofByAssignment :=
  fun {V : Set} `{EqDec_eq V} {x : Formula V} {y} (h: RProof x y) (a : Assignment V) => 
    FormulaByAssignment (fdisj (fneg x) y) a.

Definition rproofByPAssignment :=
  fun {V : Set} `{EqDec_eq V} {x : Formula V} {y} (h: RProof x y) (a : PAssignment V) => 
    FormulaByPAssignment (fdisj (fneg x) y) a.

(* Lemma LiteralPA_empty_None:
forall {V : Set} `{EqDec_eq V} {l : Literal V},
  LiteralByPAssignment   l empty_pa = None. *)

(* Lemma FormulaByPA_empty_None:
forall {V : Set} `{EqDec_eq V} {f : Formula V},
  FormulaByPAssignment  f empty_pa = None.
intros V H f. induction f; intros; eauto.
admit. admit. admit. admit. 
+ destruct l; cbn in *; eauto.
+ *)

Definition LessRefine {V : Set} `{EqDec_eq V} (b a : PAssignment V) :=
  forall x, PA b x <> None -> PA a x = PA b x.

Definition LessRefine' {V : Set} `{EqDec_eq V} (b : PAssignment V) (a: Assignment V) :=
  forall x t, PA b x = Some t -> PA b x = Some (a x).

  Ltac breakAssumpt1:=
    match goal with
    | [h0 : match ?exp with _ => _ end = _ |- _ ] => 
      let heq := fresh "heq" in
      destruct exp eqn:heq; try discriminate; try contradiction
    end.
  Ltac breakAssumpt3:=
    match goal with
    | [h0 : context[match ?exp with _ => _ end] |- _ ] => 
      let heq := fresh "heq" in
      destruct exp eqn:heq; try discriminate; try contradiction
    | [ |- context[match ?exp with _ => _ end]] => 
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


  Ltac stronger_subst:=
    match goal with
    | [h0 : ?a = _, h1 : ?a = _ |- _] =>
      rewrite h0 in *; clear h0
      end.

Lemma refinement_invariance: forall {V : Set} `{EqDec_eq V} {c} {b a}
  (hlr : LessRefine b a)  {t},
  FormulaByPAssignment c b = Some t ->
  FormulaByPAssignment c a = Some t.
  intros V H c. 
  induction c; intros; intros; cbn in *; eauto.
  + destruct l; cbn in *; try erewrite hlr; subst; eauto;
  intro hwrongeq; try rewrite hwrongeq in *; try discriminate.
  + 
    repeat breakAssumpt1; repeat stronger_subst; subst; eauto; try_injection; subst; eauto;
    repeat (erewrite IHc1; eauto; fail || erewrite IHc2; eauto; fail).
    erewrite IHc1;  eauto; cbn in *.  repeat breakAssumpt3; eauto.
    erewrite IHc2;  eauto; cbn in *.  repeat breakAssumpt3; eauto.    +     
    repeat breakAssumpt1; repeat stronger_subst; subst; eauto; try_injection; subst; eauto;
    repeat (erewrite IHc1; eauto; fail || erewrite IHc2; eauto; fail).
    erewrite IHc1;  eauto; cbn in *. repeat breakAssumpt3; eauto. 
    erewrite IHc2;  eauto; cbn in *. repeat breakAssumpt3; eauto.  
+ repeat breakAssumpt1.
    repeat (erewrite IHc; eauto; fail).
Qed.


Ltac simpl_bool:=
  cbn in *; repeat 
  match goal with
  | [|- context[andb _ false]] =>
    rewrite Bool.andb_false_r in *
  | [|- context[orb _ true]] =>
    rewrite Bool.orb_true_r in *
  end; cbn in *.

Lemma refinement'_invariance: forall {V : Set} `{EqDec_eq V} {c} {b a}
  (hlr : LessRefine' b a)  {t},
  FormulaByPAssignment c b = Some t ->
  FormulaByAssignment c a = t.
  intros V H c. 
  induction c; intros; intros; cbn in *;try_injection; subst; try reflexivity. 
  + destruct l; cbn in *. erewrite hlr in *; subst; eauto.
  try_injection; subst; eauto.
  repeat breakAssumpt1; try_injection; subst. erewrite hlr in *; subst; eauto.
  try_injection; subst; eauto.
  + repeat breakAssumpt1; try_injection; subst; eauto;  
    try (repeat (erewrite IHc1; eauto);
    repeat stronger_subst; subst; cbn in *; eauto; fail);
    try (repeat (erewrite IHc2; eauto);
    repeat stronger_subst; subst; cbn in *; eauto).  
    simpl_bool; cbn in *; eauto.
  + repeat breakAssumpt1; try_injection; subst; eauto;  
    try (repeat (erewrite IHc1; eauto);
    repeat stronger_subst; subst; cbn in *; eauto; fail);
    try (repeat (erewrite IHc2; eauto);
    repeat stronger_subst; subst; cbn in *; eauto).  
    simpl_bool; cbn in *; eauto. 
   + repeat breakAssumpt1.
    repeat (erewrite IHc; eauto); try_injection; subst; eauto.

Qed.

Lemma LessRefine_inductive:
  forall {V : Set} `{EqDec_eq V} {x : PAssignment V}  {f h v b},
  LessRefine (existT _ f h) x ->
  LiteralByPAssignment (ToLiteral v b) x = Some true ->
  forall (e :f v = None),
  LessRefine (existT _ (addAssignment v b f) (assign_fa v b h e)) x.
  unfold LessRefine. unfold addAssignment in *.
  unfold LiteralByPAssignment in *. unfold ToLiteral in *.
  intros.
  destruct (eq_dec x0 v); subst; cbn in *. 
  destruct (eq_dec v v); subst; try discriminate; try contradiction.
  repeat breakAssumpt1; subst. injection heq; intros;subst; eauto.
  injection heq; intros; subst; eauto. destruct b0; intros; try discriminate; try contradiction. eauto.
  repeat breakAssumpt1; subst;
  destruct (eq_dec x0 v); subst; cbn in *; try discriminate; try contradiction;
  try eapply H0; eauto.
Qed.

Lemma LessRefine'_inductive:
  forall {V : Set} `{EqDec_eq V} {x : Assignment V}  {f h v b},
  LessRefine' (existT _ f h) x ->
  LiteralByAssignment (ToLiteral v b) x =  true ->
  forall (e :f v = None),
  LessRefine' (existT _ (addAssignment v b f) (assign_fa v b h e)) x.

  unfold LessRefine'. unfold addAssignment in *.
  unfold LiteralByAssignment in *. unfold ToLiteral in *.
  intros; cbn in *;
  repeat breakAssumpt1; try_injection; subst; eauto;
  try injection heq0; intros;subst; eauto; try erewrite H1; eauto.
  destruct (x v0); subst; eauto; try discriminate; try contradiction.
Qed.


Lemma EvaluationSuccess_LessRefine: 
  forall {V : Set} `{EqDec_eq V} {y} {x : PAssignment V}  ,
  FormulaByPAssignment (LiteralsFormPA y) x = Some true ->
  LessRefine y x.
  intros V H y.
  destruct y as [f hf].
  induction hf; cbn in *; intros; eauto.
  + unfold LessRefine. intros. cbn in *. unfold emptyAssignment in *. 
    try contradiction.
  + repeat breakAssumpt1.
    destruct b0; destruct b1; subst; try discriminate; try contradiction. 
    pose (IHhf _ heq1).
    try eapply LessRefine_inductive; eauto.
  Qed.


Lemma EvaluationSuccess_LessRefine': 
  forall {V : Set} `{EqDec_eq V} {y} {x : Assignment V}  ,
  FormulaByAssignment (LiteralsFormPA y) x = true ->
  LessRefine' y x.
  intros V H y.
  destruct y as [f hf].
  induction hf; cbn in *; intros; eauto.
  + unfold LessRefine'. intros. cbn in *. unfold emptyAssignment in *. 
    try contradiction; try discriminate.
  + destruct (LiteralByAssignment (ToLiteral v b) x) eqn:heq0; 
    destruct (FormulaByAssignment (LiteralsForm hf) x) eqn:heq1; 
    subst; try discriminate; try contradiction. 
    pose (IHhf _ heq1).
    try eapply LessRefine'_inductive; eauto.
  Qed.

     


Lemma PAAsImplies_trans: forall {V : Set} `{EqDec_eq V} {a} {c : Formula V} {b},
  FormulaByPAssignment (LiteralsFormPA b) a = Some true ->
  FormulaByPAssignment c b = Some true ->
  FormulaByPAssignment c a = Some true.
  intros V H a c b h.
  pose (EvaluationSuccess_LessRefine h).
  intros. eapply refinement_invariance; eauto.
Qed.

(* Definition LiftAtoPA (a : Assignment V) : PAssignment V :=
   *)

Lemma PAAsImplies_trans2: forall {V : Set} `{EqDec_eq V} {a : Assignment V} {b},
  FormulaByAssignment (LiteralsFormPA b) a = true -> forall c,
  FormulaByPAssignment c b = Some true ->
  FormulaByAssignment c a = true.
  intros V H a c h b.
  pose (EvaluationSuccess_LessRefine' h).
  intros. eapply refinement'_invariance; eauto.
Qed.


Lemma PAAsImplies_true: forall {V : Set} `{EqDec_eq V} {d} {C : Formula V} ,
FormulaByPAssignment C d = Some true -> forall a,
FormulaByAssignment (fdisj (fneg (LiteralsFormPA d)) C) a = true.
cbn in *.
intros V H d C h0 assign.
destruct (FormulaByAssignment C assign) eqn:heq0;
destruct (FormulaByAssignment (LiteralsFormPA d) assign) eqn:heq1;
cbn in *; try eauto.
pose (PAAsImplies_trans2 heq1 C). eauto.
Qed.



Lemma PAAsImplies_false: forall {V : Set} `{EqDec_eq V} {d} {C : Formula V} ,
FormulaByPAssignment C d = Some false -> forall a,
FormulaByAssignment (fdisj (fneg (LiteralsFormPA d)) (fneg C)) a = true.
intros V H d C h.
assert (FormulaByPAssignment (fneg C) d = Some true); [cbn in *; rewrite h in *; try reflexivity | idtac].
intros. eapply PAAsImplies_true; eauto.
Qed.


Lemma FormulaByPA_ClauseByPA: forall  {V : Set} `{EqDec_eq V} {c : Clause V} {d},
FormulaByPAssignment (ClauseFormula c) d =
  ClauseByPAssignment c d.



intros V h c.
induction c; intros; cbn in *; eauto;subst; repeat breakAssumpt3; subst; repeat stronger_subst; eauto;
try(rewrite IHc in *; repeat stronger_subst; eauto; try discriminate; fail).


Qed.

Lemma PAAsImplies_Clause_true: forall {V : Set} `{EqDec_eq V} {c : Clause V} {d},
ClauseByPAssignment c d = Some true -> forall a,
FormulaByAssignment (fdisj (fneg (LiteralsFormPA d)) (ClauseFormula c)) a = true.
intros. eapply PAAsImplies_true. cbn in *.
  rewrite FormulaByPA_ClauseByPA in *; eauto.
Qed.

Lemma PAAsImplies_Clause_false: forall {V : Set} `{EqDec_eq V} {c : Clause V} {d},
ClauseByPAssignment c d = Some false -> forall a,
FormulaByAssignment (fdisj (fneg (LiteralsFormPA d)) (fneg (ClauseFormula c))) a = true.
intros. eapply PAAsImplies_false. cbn in *.
  rewrite FormulaByPA_ClauseByPA in *; eauto.
Qed.


Ltac clean_pose hk :=
  let h2 := fresh "h" in 
  pose hk as h2; generalize h2;
  clear h2; intro h2.

Proposition RProofSound: 
  forall {V : Set} `{EqDec_eq V} {x : Formula V} {y}
         (h : RProof x y) (a: Assignment V),
   FormulaByAssignment (fdisj (fneg x) y) a = true.
intros V H x y h.
induction h; intros assign; cbn in *;
(* Proof by Enumerating Truthtable *)
try (((repeat match goal with
| [h : (forall _:Assignment V,_)  |- _] =>
  clean_pose (h assign); clear h
end);
(repeat match goal with
|  |- context[FormulaByAssignment ?x ?a] =>
    let heq := fresh "heq" in
    destruct (FormulaByAssignment x a) eqn:heq; subst;
    try rewrite heq in *
end);
subst; cbn in *; try reflexivity);
repeat match goal with
| [h : FormulaByAssignment ?x ?a = _ |- _] =>
    rewrite h in *; cbn in *; clear h
end;
try contradiction; try discriminate);
(* Case : ClauseByPAssignment *)
(try pose (PAAsImplies_Clause_true e assign); 
try pose (PAAsImplies_Clause_false e assign);
cbn in *;
repeat match goal with
| [h : FormulaByAssignment ?x ?a = _ |- _] =>
    rewrite h in *; cbn in *; clear h
end; try discriminate; try contradiction).
(* Case : FormulaByPAssignment *)
pose (PAAsImplies_false e assign); cbn in *; 
try(repeat match goal with
| [h : FormulaByAssignment ?x ?a = _ |- _] =>
    rewrite h in *; cbn in *; clear h
end; subst; eauto; fail).
Admitted.


Definition RProofl {V : Set} `{EqDec_eq V} (h : Formula V) (c : Literal V) := RProof h (flit c).

(* Lemma RProoflid  *)

(* This one is go *)
Proposition RProoflSound:
  forall {V : Set} `{EqDec_eq V} {x : Formula V} {y}
    (h : RProofl x y) (a: Assignment V),
    FormulaByAssignment (fdisj (fneg x) (flit y)) a = true.
intros. eapply RProofSound. unfold RProofl in *. eauto.
Qed.