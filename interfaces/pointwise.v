Require Import theory.set abstract_algebra.
Require Import set_lambda.

Import projection_notation.

(** Lifting of operations on sets to functions into the sets. *)

(** The lift of an arity 1 function is just post-composition. *)
Definition pointwise_func `(f:X ⇾ Y) (D:set) : (D ⇾ X) ⇾ (D ⇾ Y) := (f ∘).

(** The lift of an arity 2 function cannot be defined in general.
  It is possible whenever the operation is strong, and also whenever
  the domain has affirmative equality. *)

Definition PointwiseOp `(f:X ⊗ Y ⇾ Z) (D:set) :=
  @IsFun ((D ⇾ X) ⊗ (D ⇾ Y) ⊗ D) Z (λ p, f (π₁ (π₁ p) (π₂ p), π₂ (π₁ p) (π₂ p))).
Existing Class PointwiseOp.

Definition pointwise_op `(f:X ⊗ Y ⇾ Z) (D:set) {H:PointwiseOp f D}
  := curry (@make_fun _ _ _ H).

Lemma StrongOp_PointWiseOp `{f:X ⊗ Y ⇾ Z} {D} `{!StrongOp f} : PointwiseOp f D.
Proof. apply (uncurry set:(λ p : (D ⇾ X) ⊗ (D ⇾ Y), λ x:D, f (π₁ p x, π₂ p x))). Qed.

Lemma AffEq_PointWiseOp `{f:X ⊗ Y ⇾ Z} {D} `{!AffirmativeEquality D} : PointwiseOp f D.
Proof. apply (uncurry set:( (λ '(g, h), λ (x:D), f (g x, h x)) : (D ⇾ X) ⊗ (D ⇾ Y) → _ )). Qed.

Global Hint Extern 10 (PointwiseOp _ _) => simple notypeclasses refine StrongOp_PointWiseOp : typeclass_instances.
Global Hint Extern 11 (PointwiseOp _ _) => simple notypeclasses refine AffEq_PointWiseOp : typeclass_instances.

