Require Import interfaces.aprop theory.set.
Require Import interfaces.set_lambda.notation.

(** Define 𝒫 X ≡ subset X to be convertible to X ⇾ Ω.
    We give subsets a type with a distinct name to enable coercions specific to subsets. *)

Definition subset (X:set) := func X Ω.
Abbreviation 𝒫 := subset.
Identity Coercion subset_func : subset >-> func.
Global Hint Extern 2 (Equiv (subset ?X)) => change (Equiv (func X AProp_set)) : typeclass_instances.

Declare Scope subset_scope.
Delimit Scope subset_scope with subset.
Bind Scope subset_scope with subset.

Canonical Structure subset_set (X:set) := {| set_T := subset X; set_eq := func_ext_eq; set_is_set := func_is_set |}.
Notation "'𝒫'" := subset_set (only printing).

Definition subset_comprehension {X : set} : ∀ (f : X → Ω) {H:SetLambdaDerivation f}, 𝒫 X := @func_make X Ω.

Notation "{ x | P }" := (subset_comprehension (fun x => P)) (x binder, only parsing) : set_scope.
Notation "{ x : T | P }" := (subset_comprehension (X:=T%type) (fun x : T => P)) (x binder, only parsing) : set_scope. 
Notation "{ x : T | P }" := (subset_comprehension (fun x : T => P)) (x binder, only printing) : set_scope.

(** Pretty-printing for binary destructuring subset comprehensions. *)
Notation "{ ' '(' a ',' b ')' : T | P }" :=
  (subset_comprehension (fun pat : T => let p := pat in let a := proj1 p in let b := proj2 p in P))
  (only printing,
   format "{  ''' '(' a ','  b ')'  :  T  |  P  }") : set_scope.

(** Pretty-printing for doubly-nested binary destructuring subset comprehensions. *)
Notation "{ ' '(' '(' x1 ',' y1 ')' ',' '(' x2 ',' y2 ')' ')' : T | P }" :=
  (subset_comprehension (fun pat : T =>
   let z := pat in
   let a := proj1 z in let b := proj2 z in
   let w := a in let x1 := proj1 w in let y1 := proj2 w in
   let v := b in let x2 := proj1 v in let y2 := proj2 v in
   P))
  (only printing,
   format "{  ''' '(' '(' x1 ','  y1 ')' ','  '(' x2 ','  y2 ')' ')'  :  T  |  P  }") : set_scope.


