Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Logic.Decidable.
(* Here we construct the relationship between  *)


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
| fbot  : Formula V
.


Arguments flit {V}.
Arguments fconj {V}.
Arguments fdisj {V}.
Arguments fneg {V}.
Arguments fbot {V}.

Definition Assignment (V:Set) := V -> bool.

Definition emptyAssignment {V : Set} : (V -> option bool) := fun _ => None.
Definition addAssignment   {V : Set} `{EqDec V} v b f : (V -> option bool) :=
  fun k =>
    match (equiv_dec k v) with
    | left _ => Some b
    | right _ => f k
    end.



(* Make a trivial partial assignment inductively defined *)
(* So that it is a finite/inductable partial assignment *)
Inductive FiniteAssignment {V : Set} `{EqDec V}: (V -> option bool) -> Prop :=
  | empty_fa : FiniteAssignment emptyAssignment
  | assign_fa : forall {f} (v : V) (b : bool), 
    FiniteAssignment f -> 
    f v = None ->
    FiniteAssignment (addAssignment v b f).

Hint Constructors FiniteAssignment Formula Literal.

Definition PAssignment (V:Set) `{EqDec V} := {f:V -> option bool | FiniteAssignment f}.

Definition PA {V:Set} `{EqDec V} (f : PAssignment V) (v : V) := proj1_sig f v.


Definition empty_pa  {V: Set} `{EqDec V}: PAssignment V := (exist _ emptyAssignment empty_fa).
Definition assign_pa {V: Set} `{EqDec V} (v : V) (b : bool) (fp : PAssignment V) (h : PA fp v = None): PAssignment V.
  destruct fp as ( f & p ). cbn in *.
  pose (addAssignment v b f) as f'.
  exact (exist _ f' (assign_fa v b p h)).
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

Definition LiteralByPAssignment {V : Set} `{EqDec V} (c : Literal V) (a : PAssignment V) : option bool :=
  match c with
  | positive k => (PA a k)
  | negative k => match PA a k with 
                  | Some k => Some (negb k)
                  | None => None 
  end
  end.

Definition ClauseByAssignment {V} (c : Clause V)  (a : Assignment V): bool.
Admitted.
Definition ClauseByPAssignment {V : Set} `{EqDec V} (c : Clause V) (a : PAssignment V): option bool.
Admitted.

Definition CNFByAssignment {V} (c : CNF V)  (a : Assignment V): bool.
Admitted.
Definition CNFByPAssignment {V : Set} `{EqDec V} (c : CNF V) (a : PAssignment V): option bool.
Admitted.

Fixpoint FormulaByAssignment {V} (c : Formula V)  (s : Assignment V): bool:=
  let rec c := FormulaByAssignment c s in
  match c with 
  | flit  a => LiteralByAssignment a s
  | fconj a b => andb (rec a) (rec b)
  | fdisj a b => orb (rec a) (rec b)
  | fneg  a => negb (rec a)
  | fbot    => false
  end.
Fixpoint FormulaByPAssignment {V: Set} `{EqDec V} (c : Formula V) (s : PAssignment V): option bool :=
  let rec c := FormulaByPAssignment c s in
  match c with 
  | flit  a => LiteralByPAssignment a s
  | fconj a b => 
      match (rec a), (rec b) with 
      | Some a, Some b => Some (andb a b)
      | _, _ => None
      end
  | fdisj a b => 
      match (rec a), (rec b) with 
      | Some a, Some b => Some (orb a b)
      | _, _ => None
      end
  | fneg  a => 
      match rec a with
      | Some a => Some (negb a)
      | _ => None 
      end
  | fbot    => Some false
  end.


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

Inductive RProof {V: Set}: Formula V -> Formula V -> Set :=
  | id : forall x, RProof x x
  | trans : forall x y z,
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
  | weaken : forall X K,
      RProof (fconj X K) X
  (* Used by Unit Propagation and backjump 
      we need to collect one clause out in unit propagation
  *)
  | weaken2 : forall X K Y,
      RProof X Y -> RProof (fconj K X) Y 
  | weaken3 : forall X Y K,
      RProof X Y -> RProof (fconj K X) (fconj K Y)
  (* Used by Decide *)
  | contra : forall N C,
      RProof (fconj N (fconj C (fneg C))) fbot
  | rconj: forall X Y Z,
      RProof X Y ->
      RProof X Z ->
      RProof X (fconj Y Z).

Definition rproofByAssignment :=
  fun {V : Set} {x : Formula V} {y} (h: RProof x y) (a : Assignment V) => 
    FormulaByAssignment (fdisj (fneg x) y) a.

Definition rproofByPAssignment :=
  fun {V : Set} `{EqDec V} {x : Formula V} {y} (h: RProof x y) (a : PAssignment V) => 
    FormulaByPAssignment (fdisj (fneg x) y) a.


Proposition RProofSound: 
  forall {V} {x : Formula V} {y}
         (h : RProof x y) (a: Assignment V),
   FormulaByAssignment (fdisj (fneg x) y) a = true.
Admitted.

Definition RProofl {V} (h : Formula V) (c : Literal V) := RProof h (flit c).

(* Lemma RProoflid  *)

(* This one is go *)
Proposition RProoflSound:
  forall {V} {x : Formula V} {y}
    (h : RProofl x y) (a: Assignment V),
    FormulaByAssignment (fdisj (fneg x) (flit y)) a = true.
Admitted.