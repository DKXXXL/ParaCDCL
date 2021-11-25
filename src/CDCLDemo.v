Require Import src.rproof.
Require Import src.CDCLtransition.
Require Import  Coq.Strings.String.
Require Import  Coq.Lists.List.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Coq.extraction.Extraction.
Extraction Language OCaml.



Instance EqDec_eq_of_Str: EqDec_eq string.
unfold EqDec_eq. 
intros. eapply string_dec.
Qed.


Class Show A : Type :=
    show : A -> string.

Instance showString : Show string :=
{
  show := id
}.

Notation p := positive.
Notation n := negative.

Instance showLiteral {V: Set} `{Show V} : Show (Literal V) :=
{
  show := 
    fun x => match x with 
              | p a => show a 
              | n a => append "~" (show a)
    end 
}.
Open Scope list_scope.
Open Scope string_scope.

Instance showClause {V: Set} `{Show V} : Show (Clause V) :=
{
  show := fun input =>
    let fix showC l : string :=
    match l with
    | nil => ""
    | cons h t => append (append (show h) ",") (showC t)
    end 
    in append "[" (append (showC input) "]")
}.
Instance showCNF {V: Set} `{Show V} : Show (CNF V) :=
{
  show := fun input =>
    let fix showCNF l : string :=
    match l with
    | nil => ""
    | cons h t => append (append (show h) ",") (showCNF t)
    end 
    in  append "{" (append (showCNF input) "}")
}.


Instance showBool : Show bool :=
{
  show := fun x =>
    match x with
    | true => "⊤"
    | false => "⊥"
    end
}.

Definition showSingleAssignment {V:Set} `{Show V} (v:V) (b:bool) := 
  append "[" (append (show v) (append ":=" (append (show b) "]"))).


Instance showFiniteAssignment {V: Set} `{Show V} `{EqDec_eq V} {h : V -> option bool} : (Show (FiniteAssignment h)).
unfold Show. intros fa.
induction fa.
exact "∅".
exact (append (showSingleAssignment v b) IHfa).
Defined.
Print showFiniteAssignment.

Instance showPAssignment {V: Set} `{Show V} `{EqDec_eq V}: (Show (PAssignment V)).
unfold PAssignment. unfold Show.
intros [f1 f2]. exact (show f2).
Defined.


Import VanillaCDCL.
Import CDCLtransition.
Definition VanillaCDCLAlg 
(fuel : nat) (f: CNF string):  
{g | CNFByPAssignment f g =  Some true} 
+ RProof (CNFFormula f) fbot
+ {l2 & {st2 : CDCLState f l2 |  ~ FinalState st2 /\ ~ ConflictingState st2}}.
eapply (VanillaCDCL.Main.CDCLAlg fuel).
Qed.

Section DemoExample.

Definition PrintVanillaCDCLAlg
(fuel : nat) (f: CNF string):  
string.
destruct (VanillaCDCLAlg fuel f) as [[result1 | noresult] | noresult].

+ destruct result1 as [pa h].
  exact (show pa).
+ exact (append (show f) (append "⊢"  "⊥")).
+ exact ("Cannot Finish").
Qed.  




(* Open Scope list_scope.
Open Scope string_scope.

 *)

 Notation p := positive.
 Notation n := negative.
 Import ListNotations.
Definition VanillaCDCLAlg' := PrintVanillaCDCLAlg 2000.

Example ex1:=
VanillaCDCLAlg' ([[p "a"; n "a"]]).

Eval lazy in  ex1.


End DemoExample.


Extraction "CDCLCompute.ml" ex1.

