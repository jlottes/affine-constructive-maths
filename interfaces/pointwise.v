Require Import theory.set abstract_algebra.
Require Import set_lambda.

Import projection_notation.

(** Lifting of operations on sets to functions into the sets. *)

(** The lift of an arity 1 function is just post-composition. *)
Definition pointwise_func@{u} {X Y:set@{u}} (f:X ⇾ Y) (D:set@{u}) : (D ⇾ X) ⇾ (D ⇾ Y) := (f ∘).

(** The lift of an arity 2 function cannot be defined in general.
  It is possible whenever the operation is strong, and also whenever
  the domain has affirmative equality. *)

Definition PointwiseOp@{u} {X Y Z:set@{u}} (f:X ⊗ Y ⇾ Z) (D:set@{u}) :=
  @IsFun ((D ⇾ X) ⊗ (D ⇾ Y) ⊗ D) Z (λ p, f (π₁ (π₁ p) (π₂ p), π₂ (π₁ p) (π₂ p))).
Existing Class PointwiseOp.

Definition pointwise_op@{u} {X Y Z:set@{u}} (f:X ⊗ Y ⇾ Z) (D:set@{u}) {H:PointwiseOp f D}
  := curry (@func_make _ _ _ H).

Lemma StrongOp_PointWiseOp@{u} {X Y Z D:set@{u}} {f:X ⊗ Y ⇾ Z} `{!StrongOp f} : PointwiseOp f D.
Proof. apply (uncurry set:(λ '(g,h) : (D ⇾ X) ⊗ (D ⇾ Y), λ x:D, f (g x, h x))). Qed.

Lemma AffEq_PointWiseOp@{u} {X Y Z D:set@{u}} {f:X ⊗ Y ⇾ Z} `{!AffirmativeEquality D} : PointwiseOp f D.
Proof. apply (uncurry set:( (λ '(g, h) : (D ⇾ X) ⊗ (D ⇾ Y), λ x:D, f (g x, h x)) )). Qed.

Global Hint Extern 10 (PointwiseOp _ _) => simple notypeclasses refine StrongOp_PointWiseOp : typeclass_instances.
Global Hint Extern 11 (PointwiseOp _ _) => simple notypeclasses refine AffEq_PointWiseOp : typeclass_instances.

