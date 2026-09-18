Require Import theory.set logic.aprop logic.relations.
Require Import easy rewrite.

Global Hint Extern 2 (IsSet _ (e:=leq)) => simple notypeclasses refine (leq_equiv _) : typeclass_instances.
Definition default_set_make A := set_make A (set_eq:=leq).

Class DefaultEquality (X:set) : SProp :=
  default_equality (x y : X) : x = y ⧟ leq (x, y).

Lemma default_set_make_prop {A} : DefaultEquality (default_set_make A).
Proof. hnf; now intros. Qed.
Global Hint Extern 2 (DefaultEquality (default_set_make _)) => simple notypeclasses refine default_set_make_prop : typeclass_instances.

Lemma default_equality_affirmative `{DefaultEquality X} : AffirmativeEquality X.
Proof. intros [x y]. now rew (default_equality _ _). Qed.
Coercion default_equality_affirmative : DefaultEquality >-> AffirmativeEquality.
Global Hint Extern 2 (AffirmativeEquality (default_set_make _)) => simple notypeclasses refine default_set_make_prop : typeclass_instances.

Lemma default_equality_is_fun@{u} {X Y:set@{u}} {f} `{!DefaultEquality X} : @IsFun X Y f.
Proof. intros x y. apply affirmative_aimpl. rew (default_equality _ _). now intros []. Qed.
Global Hint Extern 2 (IsFun (X:=default_set_make _) _) => simple notypeclasses refine default_equality_is_fun : typeclass_instances.

Definition default_eq_func@{u} {X Y : set@{u}} (f:X → Y) `{!DefaultEquality X}
  := @func_make X Y f default_equality_is_fun.

Import projection_notation.

Section products.
  Universes u.
  Lemma DefaultEquality_tensor {X Y:set@{u}} `{HX:DefaultEquality X} `{HY:DefaultEquality Y} : DefaultEquality (X ⊗ Y).
  Proof. intros [x₁ y₁][x₂ y₂]. split.
  + unfold_pair_eq. apply affirmative_aimpl.
    rew ?(default_equality _ _). now intros [[][]].
  + apply affirmative_aimpl. now intros [].
  Qed.
End products.

Global Hint Extern 2 (DefaultEquality (_ ⊗ _)) => simple notypeclasses refine DefaultEquality_tensor : typeclass_instances.

