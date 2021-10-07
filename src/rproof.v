(* Here we construct the relationship between  *)


Inductive Literal (V : Set) : Set :=
| pos : V -> Literal V
| neg : V -> Literal V.




Inductive Formula (V: Set) : Set :=
| lit  : Literal V -> Formula V
| conj : Formula V -> Formula V -> Formula V
| disj : Formula V -> Formula V -> Formula V
| neg  : Formula V -> Formula V
| bot  : Formula V
.


Definition Assignment (V:Set) := V -> bool.

Definition emptyAssignment {V : Set} : (V -> Some bool) := fun _ => none.
Definition addAssignment   {V : Set} v b f : (V -> Some bool) :=
  fun k =>
    match (eq_dec k v) with
    | true => Some bool 
    | false => f k
    end.



(* Make a trivial partial assignment inductively defined *)
(* So that it is a finite/inductable partial assignment *)
Inductive FiniteAssignment {V : Set} : (V -> Some bool) -> Prop :=
  | empty_fa : FiniteAssignment emptyAssignment
  | assign_fa : forall (v : V) {b : bool}, 
    FiniteAssignment f -> 
    f b = None ->
    FiniteAssignment V (addAssignment v b f).

Definition PAssignment (V:Set) := {f:V -> Some bool | FiniteAssignment x}


Definition empty_pa  {V: Set} : PAssignment V := (exist emptyAssignment empty_fa).
Definition assign_pa {V: Set} v b (fp : PAssignment V) (h : ): PAssignment V := 
  match fp with
  | exist f p => 


Notation "∅" := empty_pa.


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

Definition FormulaByAssignment {V} (c : Formula V)  (a : Assignment V): bool.
Admitted.
Definition FormulaByPAssignment {V} (c : Formula V) (a : PAssignment V): option bool.
Admitted.


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
  | res : forall 
      RProof M (disj C L) ->
      RProof M (neg C)
      RProof M L 
  (* Used by Unit Propagation and backjump *)
  | weaken : forall X K Y,
      RProof X Y -> RProof (conj X K) Y 
  (* Used by Decide *)
  | contra : forall
      RProof (conj N (conj C (neg C))) bot
  | weaken2 :
      RProof (conj X K) Y ->
      RProof Q K ->
      RProof (conj X Q) Y
  | weaken3 :
      RProof (conj X K) X
  | conj:
      RProof X Y ->
      RProof X Z ->
      RProof X (conj Y Z).

Definition rproofByAssignment :=
  fun {V} {x : Formula V} {y} (h: RProof x y) (a : Assignment V) => 
    FormulaByAssignment (disj (neg x) y) a.

Definition rproofByPAssignment :=
  fun {V} {x : Formula V} {y} (h: RProof x y) (a : PAssignment V) => 
    FormulaByPAssignment (disj (neg x) y) a.


Proposition RProofSound: 
  forall {V} {x : Formula V} {y}
         (h : RProof x y) (a: Assignment V),
   FormulaByAssignment (disj (neg x) y) a = true.
Admitted.

Definition RProofl {V} (h : Formula V) (c : Literal V) := RProof h (lit c).

(* Lemma RProoflid  *)

(* This one is go *)
Proposition RProoflSound:
  forall {V} {x : Formula V} {y}
    (h : RProofl x y) (a: Assignment V),
    FormulaByAssignment (disj (neg x) (lit y)) a = true.