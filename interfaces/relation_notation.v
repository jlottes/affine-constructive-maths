Require Export interfaces.notation interfaces.aprop.

Set Typeclasses Unique Instances.

Declare Scope rel_scope.
Delimit Scope rel_scope with rel.
Global Open Scope rel_scope.

Class Equiv (A:Type) := equiv : A ∗ A → Ω.
Notation "x = y :> A" := (@equiv A _ (@pair A A x y)) (only parsing) : rel_scope.
Notation "x = y" := (equiv (x, y)) : rel_scope.
Notation "(=)" := (equiv) (only parsing) : rel_scope.
Notation "x ≠ y :> A" := (anot (x = y :> A)) : rel_scope.
Notation "x ≠ y" := (anot (x = y)) : rel_scope.
Notation "(≠)" := (complement (=)) (only parsing) : rel_scope.
Global Hint Mode Equiv + : typeclass_instances.

Class Le (A:Type) := le : A ∗ A → Ω.
Notation "x ≤ y :> A" := (@le A _ (@pair A A x y)) (only parsing) : rel_scope.
Notation "x ≤ y" := (le (x, y)) : rel_scope.
Notation "(≤)" := le (only parsing) : rel_scope.
Global Hint Mode Le + : typeclass_instances.

Definition lt `{Le A} := complement (flip (@le A _)).
Notation "x < y :> A" := (@lt A _ (@pair A A x y)) (only parsing) : rel_scope.
Notation "x < y" := (lt (x, y)) : rel_scope.
Notation "(<)" := lt (only parsing) : rel_scope.

Unset Typeclasses Unique Instances.


Definition order_op (A:Type) := A.
Global Typeclasses Opaque order_op.
Global Hint Extern 2 (Le (order_op ?A)) => simple notypeclasses refine (flip (@le A _)) : typeclass_instances.
Global Hint Extern 2 (Equiv (order_op ?A)) => change (Equiv A) : typeclass_instances.

