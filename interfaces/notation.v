Require Export prelude try_all_hyps.

Reserved Notation "x → y" (at level 99, right associativity, y at level 200).
Reserved Notation "x ⊸ y" (at level 99, right associativity, y at level 200).
Reserved Notation "x ↔ y" (at level 95, no associativity).
Reserved Notation "x ⧟ y" (at level 95, no associativity).
Reserved Notation "x ≅ y" (at level 95, no associativity).
Reserved Notation "x ⇾ y" (at level 92, right associativity, y at level 200).
Reserved Notation "x ⟶ y" (at level 90, right associativity).
Reserved Notation "x ⇒ y" (at level 85, right associativity).
Reserved Notation "x ∨ y" (at level 85, right associativity).
Reserved Notation "x ⊞ y" (at level 85, right associativity).
Reserved Notation "x ∧ y" (at level 80, right associativity).
Reserved Notation "x ⊠ y" (at level 80, right associativity).
Reserved Notation "¬ x" (at level 75, right associativity).

Reserved Notation "x = y :> T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "x ≠ y" (at level 70, no associativity).

Reserved Notation "x ≡ y :> T"
(at level 70, y at next level, no associativity).
Reserved Notation "x ≡ y" (at level 70, no associativity).
Reserved Notation "x ≣ y" (at level 70, no associativity).

Reserved Notation "x ≤ y :> T"
(at level 70, y at next level, no associativity).
Reserved Notation "x ≤ y" (at level 70, no associativity).
Reserved Notation "x < y" (at level 70, no associativity).
Reserved Notation "x ⊆ y" (at level 70, no associativity).

Reserved Notation "x ⊔ y" (at level 59, left associativity).
Reserved Notation "x ⊓ y" (at level 54, left associativity).

Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x - y" (at level 50, left associativity).
Reserved Notation "x ⊕ y" (at level 50, left associativity).
Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x × y" (at level 40, left associativity).
Reserved Notation "x · y" (at level 40, left associativity).
Reserved Notation "x ⊗ y" (at level 40, left associativity).
Reserved Notation "x ∙ y" (at level 40, left associativity).
Reserved Notation "- x" (at level 35, right associativity).
Reserved Notation "( x , y , .. , z )" (at level 0).

Reserved Notation "x || y" (at level 50, left associativity).
Reserved Notation "x && y" (at level 40, left associativity).

Reserved Notation "g ∘ f" (at level 30, left associativity).
Reserved Notation "g ⊚ f" (at level 30, left associativity).

Reserved Notation "x ⁻¹" (at level 1, format "x ⁻¹").

Notation "'∀' x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity).

Notation "A → B" := (∀ _ : A, B) : type_scope.

Infix "*" := tprod : type_scope.
Notation "( a , b , .. , c )" := (pair .. (pair a b) .. c ).
Module projection_notation.
  Notation π₁ := proj1.
  Notation π₂ := proj2.
End projection_notation.

Module sigma_notation.
  Notation "'Σ' x .. y , P" := (tsig (fun x => .. (tsig (fun y => P)) ..))
    (at level 200, x binder, y binder, right associativity) : type_scope.
End sigma_notation.

Module tsum_notation.
  Infix "+" := tsum : type_scope.
End tsum_notation.


Reserved Notation "{ x | P }" (at level 0, x at level 99 as name).
Reserved Notation "{ x : A | P }" (at level 0, x at level 99 as name).

Set Typeclasses Unique Instances.

(** Notation for the unique term of some type. *)
Declare Scope the_scope.
Delimit Scope the_scope with the.

Class The X := the : X.
Notation "!" := the : the_scope.
Global Hint Mode The + : typeclass_instances.
Global Typeclasses Transparent The.

(** Notations for categories *)
Declare Scope cat_scope.
Delimit Scope cat_scope with cat.
(*Global Open Scope cat_scope.*)

Class BoldZero Ob := bzero : Ob.
Notation "𝟎" := bzero : cat_scope.
Global Hint Mode BoldZero + : typeclass_instances.

Class BoldOne Ob := bone : Ob.
Notation "𝟏" := bone : cat_scope.
Global Hint Mode BoldOne + : typeclass_instances.

Class Product Ob := prod : Ob → Ob → Ob.
Notation "X × Y" := (prod X Y) : cat_scope.
Global Hint Mode Product + : typeclass_instances.

Class Tensor Ob := tensor : Ob → Ob → Ob.
Notation "X ⊗ Y" := (tensor X Y) : cat_scope.
Global Hint Mode Tensor + : typeclass_instances.

Global Typeclasses Transparent BoldZero BoldOne Product Tensor.

Global Hint Extern 1 (BoldZero Type) => refine empty : typeclass_instances.
Global Hint Extern 1 (BoldOne  Type) => refine unit  : typeclass_instances.
Global Hint Extern 1 (Product  Type) => refine tprod : typeclass_instances.

Unset Typeclasses Unique Instances.
