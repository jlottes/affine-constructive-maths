Require Export interfaces.notation interfaces.aprop.

Set Typeclasses Unique Instances.

Declare Scope rel_scope.
Delimit Scope rel_scope with rel.
Global Open Scope rel_scope.

Class Equiv@{i} (A:Type@{i}) := equiv : A → A → Ω.
Notation "x = y :> A" := (@equiv A _ x y) : rel_scope.
Notation "x = y" := (equiv x y) : rel_scope.
Notation "(=)" := (equiv) (only parsing) : rel_scope.
Notation "x ≠ y" := (anot (equiv x y)) : rel_scope.
Notation "(≠)" := (complement equiv) (only parsing) : rel_scope.
Global Hint Mode Equiv + : typeclass_instances.

Class Le@{i} (A:Type@{i}) := le : A → A → Ω.
Notation "x ≤ y :> A" := (@le A _ x y) : rel_scope.
Notation "x ≤ y" := (le x y) : rel_scope.
Notation "(≤)" := le (only parsing) : rel_scope.
Global Hint Mode Le + : typeclass_instances.

Definition lt `{Le A} := complement (flip (@le A _)).
Notation "x < y" := (lt x y) : rel_scope.
Notation "(<)" := lt (only parsing) : rel_scope.

Unset Typeclasses Unique Instances.

