Require Import interfaces.notation.

Inductive eq (A:Type) (x:A) : A → Prop :=
    eq_refl : x ≡ x :> A
where "x ≡ y :> A" := (@eq A x y) : type_scope.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Arguments eq_ind [A] x P _ a _.
Arguments eq_rec [A] x P _ a _.
Arguments eq_rect [A] x P _ a _.

Notation "x ≡ y" := (eq x y) : type_scope.

Register eq as core.eq.type.
Register eq_refl as core.eq.refl.
Register eq_ind as core.eq.ind.
Register eq_rect as core.eq.rect.
