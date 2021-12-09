Require Import src.rproof.
Require Import src.CDCLtransition.
Require Import Coq.Unicode.Utf8.
Require Import  Coq.Strings.String.
Require Import  Coq.Lists.List.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.

Require Coq.extraction.Extraction.
Extraction Language OCaml.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Constant plus =>"( + )".
Extract Constant mult => "( * )".
Extract Constant eqb => "( = )".
Extract Inductive sumbool => "bool" ["true" "false"].
(* Extract Inductive string => "string" [ """""" "(fun a b -> (string_of_char a) ^ b)"] "(fun e c s -> if s = "" then e else c s.[0] (String.sub s 1 (String.length s - 1)))". *)
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
              | n a => append "¬" (show a)
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
    | true => "T"
    | false => "F"
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
+ exact (append (show f) " ⊢ Bottom"). 
+ exact ("Cannot Finish Computing in these fuel").
Qed.  




(* Open Scope list_scope.
Open Scope string_scope.

 *)

 Notation p := positive.
 Notation n := negative.
 Import ListNotations.
Definition VanillaCDCLAlg' := PrintVanillaCDCLAlg 2000.


Example Tests : list (CNF string) := [
  [[p "a"; n "a"]];
  [[p "a"]; [n "a"]];
  [[p "a"; p "b"]; [n "a"]];
  [[n "b"; p "a"; n "a"]; [n "b"; p "a"]; [n "b"; p "a"]];
  [[p "b"; n "a"]; [p "b"; p "a"]];
  [[n "a"; p "b"]; [n "b"; p "c"]; [n "c"; p "d"]; [n "d"; p "e"]; [n "e"; p "f"]];
  [[n "a"; p "b"]; [n "a"; n "b"; p "c"]; [n "a"; n "b"; n "c"; p "d"]; [n "a"; n "b"; n "c"; n "d"; p "e"]; [n "a"; n "b"; n "c"; n "d"; n "e"; p "f"]];
  (* Small *)
  [[n "b"]; [p "a"; n "a"]];
  [[p "b"; n "b"]; [p "b"; n "a"; p "a"]];
  [[p "a"; n "a"]; [n "b"; p "a"]];
  [[n "b"]; [p "b"; n "a"]];
  [[n "b"; n "a"]; [p "a"]];
  [[n "b"; p "a"]; [p "b"; n "b"]];
  [[n "b"]; [p "b"; n "b"]];
  [[n "b"; p "a"; n "a"]; [n "b"; p "a"; n "a"]; [n "a"]];
  [[n "a"; p "b"]; [n "b"; p "c"]];
  [[n "a"; p "a"]; [p "c"; p "a"]; [n "c"]; [p "c"; n "b"]; [n "a"]; [n "c"; p "a"]];

  (* Random Small 2 *)
  [[p "a"]; [p "a"]; [n "b"; p "a"; p "b"]; [n "b"]; [n "b"; n "c"; p "b"; n "a"]; [p "a"]];
  [[n "a"; n "c"]; [n "a"; p "b"]; [p "b"]; [p "d"]];
  [[p "a"; p "b"]; [n "a"; n "b"; p "a"]; [p "a"; p "c"]; [p "a"; p "b"; p "c"]; [n "b"; p "a"; n "a"]; [n "a"]; [n "b"; n "c"; p "a"; n "d"]; [p "c"]; [n "b"; n "a"]; [n "a"]];
  [[p "a"; p "e"]; [n "a"; n "b"]; [n "b"; p "a"; p "b"]; [n "d"]; [n "f"]; [n "b"; n "d"; p "b"]];
  [[p "a"; n "d"; p "b"]; [p "b"]; [p "a"]; [n "a"]];
  [[p "c"]; [p "a"; p "b"; p "f"]; [n "c"; p "b"]; [n "a"; p "a"]; [n "c"]];
  [[n "a"]; [n "b"; n "c"; p "d"]; [n "b"; p "a"]; [p "a"; p "c"]; [n "c"; p "c"]; [n "a"; p "a"]; [n "b"; p "c"]];
  [[n "b"; p "a"; p "c"; p "d"]; [p "d"]; [n "b"]; [p "b"; p "c"]];
  [[n "a"; p "a"]; [n "d"; p "a"]; [p "a"]; [n "a"; n "c"]; [n "a"; p "b"]; [p "a"; p "b"; p "c"]; [n "a"; n "b"; n "c"; p "b"]; [n "b"; p "a"; n "a"]; [n "c"; p "a"]; [p "a"]];
  [[n "a"; p "c"]; [n "a"; n "b"; p "a"]; [n "a"; p "c"]; [p "b"]; [n "b"; p "b"]; [n "b"; p "a"]; [n "b"; p "b"]; [n "b"]; [n "a"; n "c"]];
  (* Random Larger : poisson(3) + 1 *)
  [[p "b"; n "e"; n "c"; n "d"; n "b"]; [p "d"; p "c"; p "b"; p "f"; n "c"]; [p "d"; p "c"; n "d"; n "b"; n "a"; p "i"]; [n "h"; p "a"; n "f"]; [p "d"; n "b"]; [p "c"; p "b"; n "e"; n "c"; n "b"]];
[[p "d"; n "d"; n "f"]; [p "d"; n "d"; n "c"]; [p "d"; p "c"; n "e"; p "f"; n "d"; n "c"]; [p "d"]; [p "d"; p "c"; n "e"; p "e"; n "b"]; [n "e"; n "d"; n "b"]];
[[p "f"; p "c"]; [p "e"; p "d"; p "b"; p "g"]; [p "d"; p "b"; n "e"; n "d"; n "c"]; [p "c"; n "e"; n "d"]; [p "c"; n "b"]];
[[p "e"; p "d"; n "c"]; [p "c"; n "e"; n "d"; n "c"]; [p "e"; p "d"; p "f"]; [p "d"; n "d"; p "h"; n "f"]];
[[p "d"; p "g"; n "e"]; [p "d"; n "e"; n "b"]; [p "e"; n "b"; n "d"; n "c"]; [n "e"; n "d"]; [p "i"; n "d"; n "b"]; [p "d"; n "d"; n "b"]];
[[p "d"; p "c"]; [p "d"; p "c"; p "f"; n "g"; n "b"]; [p "d"; p "c"; n "e"; n "g"; p "e"; n "b"; n "c"]; [p "d"; p "c"; n "c"; n "b"; n "a"]; [p "d"; p "c"; p "b"; n "g"; p "e"; n "d"]];
[[p "d"; p "b"; n "d"]; [p "d"; n "e"; n "d"; n "c"; n "a"; p "a"]; [p "e"; p "d"; n "e"; n "b"]; [p "c"; n "e"; p "f"; p "e"; n "d"; n "b"]; [n "h"; p "d"; p "g"; n "d"]; [p "e"; p "c"; n "c"]];
[[p "f"; p "c"; p "g"; n "k"]; [p "c"; p "h"; p "e"; n "c"; p "a"]; [p "e"; p "d"; p "c"; n "e"]; [p "d"; p "c"; n "f"; p "e"; n "c"; n "a"; p "a"]; [p "f"; p "c"; p "d"; n "b"]; [n "c"; n "f"; n "b"]; [p "e"; p "d"; p "c"; n "e"]; [p "f"; n "j"; p "b"; n "c"]; [p "b"; n "e"; n "d"; n "c"]; [p "d"; p "b"; p "e"; n "d"; n "b"; p "g"]];
[[p "d"; p "c"; n "e"; p "f"; n "b"]; [p "d"; p "c"; n "e"; p "f"; p "e"; p "a"]; [n "a"; p "f"; n "d"; n "f"]; [p "b"; n "g"; p "e"; n "b"; n "c"]; [p "d"; p "c"; n "d"]; [p "f"; p "g"]];
[[p "d"; p "b"; p "f"; n "c"; p "a"]; [p "b"; n "e"; p "h"; n "b"]; [p "f"; n "e"; n "d"; n "c"]; [p "d"; p "c"; p "a"]; [n "g"; p "c"; n "e"; n "c"]];

  (* Random Even Larger : poisson(5) + 1*)

  [[p "h"; p "c"; n "d"; n "j"; p "e"; n "g"; n "l"; n "e"]; [n "d"; n "f"; n "h"; p "d"; p "f"; n "e"; n "i"]; [n "f"; p "g"; p "e"; n "h"; n "k"; n "g"; n "b"; n "e"]; [p "n"; p "e"; n "h"; n "e"; n "c"]; [p "h"; n "d"; p "c"; p "f"; n "g"; n "b"; n "e"]];
[[p "d"; p "f"; n "e"; n "i"]; [p "h"; p "c"; n "c"; p "e"]; [n "d"; n "g"; p "c"; p "i"; n "b"; n "e"]; [n "f"; p "i"; n "d"; n "l"]; [n "d"; p "c"; p "g"; p "e"; n "g"]];
[[n "d"; p "g"; n "j"; p "b"; n "g"]; [p "h"; n "d"; p "j"; n "f"; p "k"; n "h"]; [n "f"; p "e"; n "j"; n "g"]; [p "h"; n "f"; p "g"; p "f"; n "h"; p "c"; p "d"; p "i"; n "b"; n "e"]; [p "c"; n "j"; p "e"; n "g"; p "d"]; [p "f"; p "h"; n "i"]; [p "j"; p "g"; n "g"; p "d"; p "f"]; [n "m"; n "f"; p "g"; p "e"; n "h"; n "g"]; [p "h"; n "f"; p "g"; p "e"; p "d"; p "i"; p "f"]; [n "f"; p "g"; n "k"; p "e"]];
[[n "d"; p "j"; p "k"; p "b"; p "c"; p "i"; n "e"; n "c"; n "i"]; [n "f"; p "e"; p "i"; n "e"; n "c"]; [n "f"; n "e"]; [n "d"; p "h"; n "f"; p "g"; p "e"; n "e"]];
[[p "i"; p "g"; n "d"; n "g"]; [p "g"; p "e"; p "d"; p "f"; n "e"]; [p "h"; n "f"; p "e"; p "d"; p "f"]; [p "d"; n "k"; n "g"]; [n "h"; n "d"]; [p "c"; n "f"; p "e"; n "g"; p "i"; p "f"; n "e"]];
[[n "d"; p "h"; n "g"; p "e"; p "c"; p "f"; n "e"; n "c"]; [n "d"; p "h"; p "g"; p "e"; n "h"; n "e"]; [n "i"; p "f"; p "e"]; [p "i"; p "f"; n "e"; n "d"]; [n "d"; p "g"; p "e"; n "g"; n "e"; n "c"]];
[[n "d"; p "g"; p "b"; p "d"; n "e"; n "i"]; [n "h"; p "e"; n "e"; n "g"]; [p "h"; n "f"; p "e"; n "g"; n "e"; n "i"]; [n "d"; n "f"; p "e"; p "f"; n "e"]; [n "f"; p "d"; n "l"; p "f"; n "c"; n "i"]];
[[n "d"; p "h"; p "g"; p "e"; p "f"]; [n "d"; p "h"; p "g"; p "a"; n "h"; n "g"; p "f"; n "e"]; [p "g"; p "b"; n "h"; p "a"; p "c"; p "f"; n "e"; n "c"; n "i"]; [n "d"; p "g"; p "k"; p "e"; n "e"; n "i"]; [n "d"; p "c"; p "e"]; [n "h"; n "e"; n "g"]; [p "g"; n "e"; p "b"; n "g"]; [p "j"; p "g"; p "b"; p "d"; n "e"]; [p "e"; n "g"; p "d"; p "f"; n "e"; n "c"]];
[[p "g"; n "e"; p "h"]; [p "h"; p "j"; n "g"; p "d"; p "i"]; [p "h"; p "g"; p "e"; p "d"; n "e"]; [n "d"; n "j"; p "e"; n "g"; p "d"; p "f"]; [p "h"; n "f"; p "b"; n "g"; p "i"; n "e"]; [n "h"; n "b"; n "d"]; [n "f"; p "g"; p "l"; n "h"; n "b"; p "f"]; [p "d"; p "i"; n "c"; n "i"]; [p "h"; n "f"; p "e"; p "f"; n "e"; n "i"]];
[[n "f"; p "e"; n "h"; n "b"; p "f"; n "e"; n "c"; n "i"]; [p "h"; n "j"; p "e"; n "h"; p "f"; n "e"; n "i"]; [p "h"; n "d"; p "e"; p "d"; p "i"; n "b"; n "e"; n "c"]; [n "h"; p "e"; n "b"; p "g"]; [p "k"; p "e"; n "g"; p "d"; p "f"]; [n "f"; n "l"; p "g"; p "c"]; [n "h"; p "f"; p "h"; p "e"]; [p "b"; p "e"; p "c"; p "d"; p "i"; p "f"]; [n "j"; p "e"; p "c"; p "d"; p "f"; n "e"; n "i"]; [n "d"; p "k"; p "b"; p "e"; n "g"; p "d"; p "f"; n "c"]; [n "d"; p "h"; p "j"; p "g"; p "e"; n "g"; p "f"; n "e"]]
].


Example RunTests : list string :=
  map (fun x => 
        (append 
          (show x)
          (append 
            " ===> "  
            (VanillaCDCLAlg' x)))) Tests.

End DemoExample.


Extraction "tests/CDCLTests.ml" RunTests.

