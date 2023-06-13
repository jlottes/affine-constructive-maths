Require Import theory.set logic.aprop.
Require Import easy rewrite.

Section projected_set.
  Universes i.

  Class IsProjectedSet (A:Type@{i}) {Ae:Equiv A} {Y:set@{i}} {f:A → Y} : SProp :=
    is_projected_set : ∀ x y, x = y ⧟ f x = f y.

  Definition projected_set_eq {A:Type@{i}} {Y:set@{i}} (f:A → Y) : Equiv A := λ x y, f x = f y.
  Lemma projected_set_IsProjectedSet `{f:A → set_T Y} : IsProjectedSet A (Ae:=projected_set_eq f) (f:=f).
  Proof. easy. Qed.

  Lemma projected_set_is_set `{IsProjectedSet A (f:=f) } : IsSet A. 
  Proof. split; hnf; intros; rew ?(is_projected_set (A:=A) _ _).
  + refl.
  + now apply symmetry.
  + now apply transitivity.
  Qed.
  Coercion projected_set_is_set : IsProjectedSet >-> IsSet.

  Definition projected_set_make A `{H:IsProjectedSet A} : set@{i} := set_make A.
  Definition projected_set {A:Type@{i}} {Y:set@{i}} (f:A → Y) : set@{i}
    := projected_set_make A (H:=projected_set_IsProjectedSet (f:=f)).

  Hint Extern 1 (IsProjectedSet (set_T (projected_set _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
  Hint Extern 1 (IsProjectedSet (set_T (projected_set_make _ (H:=?H)))) => notypeclasses refine H : typeclass_instances.

  Lemma projected_set_project_is_fun {X Y : set@{i}} {f:X → Y} {H:@IsProjectedSet X _ Y f} : IsFun f.
  Proof. intros ??. now rew (is_projected_set (A:=X) _ _). Qed.

  Definition projected_set_project (X:set@{i}) {Y : set@{i}} {f:X → Y} {H:@IsProjectedSet X _ Y f}
    : X ⇾ Y := @make_fun _ _ _ projected_set_project_is_fun.

  Lemma projected_set_project_injective (X:set@{i}) {Y : set@{i}} {f:X → Y} {H:@IsProjectedSet X _ Y f}
    : Injective (projected_set_project X).
  Proof. intros x y. change (f x = f y ⊸ x = y). apply is_projected_set. Qed.

  Context {X:set@{i}} `{H:IsProjectedSet X (Ae:=_) (Y:=Y) (f:=f)}.

  Lemma projected_set_strong `{!StrongSet Y} : StrongSet X.
  Proof. intros x y z. rew ?(is_projected_set (A:=X) _ _). now apply strong_transitivity. Qed.

  Lemma projected_set_dec_eq `{!DecidableEquality Y} : DecidableEquality X.
  Proof. intros x y. now rew ?(is_projected_set (A:=X) _ _). Qed.

  Lemma projected_set_aff_eq `{!AffirmativeEquality Y} : AffirmativeEquality X.
  Proof. intros x y. now rew ?(is_projected_set (A:=X) _ _). Qed.

  Lemma projected_set_ref_eq `{!RefutativeEquality Y} : RefutativeEquality X.
  Proof. intros x y. now rew ?(is_projected_set (A:=X) _ _). Qed.
End projected_set.

Global Hint Extern 1 (IsProjectedSet (set_T (projected_set _))) => notypeclasses refine projected_set_IsProjectedSet : typeclass_instances.
Global Hint Extern 1 (IsProjectedSet (set_T (projected_set_make _ (H:=?H)))) => notypeclasses refine H : typeclass_instances.
Global Hint Extern 2 (Injective (projected_set_project _)) => notypeclasses refine (projected_set_project_injective _) : typeclass_instances.
Global Hint Extern 4 (StrongSet (projected_set_make _)) => simple notypeclasses refine projected_set_strong : typeclass_instances.
Global Hint Extern 4 (StrongSet (projected_set      _)) => simple notypeclasses refine projected_set_strong : typeclass_instances.
Global Hint Extern 4 (DecidableEquality   (projected_set_make _)) => simple notypeclasses refine projected_set_dec_eq : typeclass_instances.
Global Hint Extern 4 (DecidableEquality   (projected_set      _)) => simple notypeclasses refine projected_set_dec_eq : typeclass_instances.
Global Hint Extern 4 (AffirmativeEquality (projected_set_make _)) => simple notypeclasses refine projected_set_aff_eq : typeclass_instances.
Global Hint Extern 4 (AffirmativeEquality (projected_set      _)) => simple notypeclasses refine projected_set_aff_eq : typeclass_instances.
Global Hint Extern 4 (RefutativeEquality  (projected_set_make _)) => simple notypeclasses refine projected_set_ref_eq : typeclass_instances.
Global Hint Extern 4 (RefutativeEquality  (projected_set      _)) => simple notypeclasses refine projected_set_ref_eq : typeclass_instances.

Definition projected_quotient_map `(f:X ⇾ Y) := @make_fun X (projected_set f) id (is_fun f).

Lemma project_quotient_cancel {X Y Z} (f:X ⇾ Y) (g₁ g₂ : projected_set f ⇾ Z)
  : g₁ ∘ projected_quotient_map f = g₂ ∘ projected_quotient_map f ⊸ g₁ = g₂.
Proof. refl. Qed.

Import projection_notation.

Section products.
  (*Universes i.

  Context {X Y : set@{i}}.
  Context `{HX:IsProjectedSet X (Ae:=_) (Y:=X') (f:=f)}.
  Context `{HY:IsProjectedSet Y (Ae:=_) (Y:=Y') (f:=g)}.*)

  Lemma IsProjectedSet_tensor {X Y : set} `{HX:IsProjectedSet X (Ae:=_) (Y:=X') (f:=f)} `{HY:IsProjectedSet Y (Ae:=_) (Y:=Y') (f:=g)}
  : IsProjectedSet (X ⊗ Y) (f := λ p, tensor_pair (f (π₁ p)) (g (π₂ p))).
  Proof. intros [x₁ y₁][x₂ y₂]. change (x₁ = x₂ ⊠ y₁ = y₂ ⧟ f x₁ = f x₂ ⊠ g y₁ = g y₂).
    refine (aprod_proper_aiff _ _); exact (is_projected_set _ _).
  Qed.

  Lemma IsProjectedSet_prod {X Y : set} `{HX:IsProjectedSet X (Ae:=_) (Y:=X') (f:=f)} `{HY:IsProjectedSet Y (Ae:=_) (Y:=Y') (f:=g)}
  : IsProjectedSet (X × Y) (f := λ p, prod_pair (f (π₁ p)) (g (π₂ p))).
  Proof. intros [x₁ y₁][x₂ y₂]. change (x₁ = x₂ ∧ y₁ = y₂ ⧟ f x₁ = f x₂ ∧ g y₁ = g y₂).
    refine (aand_proper_aiff _ _); exact (is_projected_set _ _).
  Qed.
End products.

Global Hint Extern 2 (IsProjectedSet (set_T (_ ⊗ _))) => notypeclasses refine IsProjectedSet_tensor : typeclass_instances.
Global Hint Extern 2 (IsProjectedSet (set_T (_ × _))) => notypeclasses refine IsProjectedSet_prod : typeclass_instances.

Section functions.
  (*Universes i.
  Context {X Y : set@{i}}.
  Context `{HX:IsProjectedSet X (Ae:=_) (Y:=X') (f:=p)}.
  Context `{HY:IsProjectedSet Y (Ae:=_) (Y:=Y') (f:=q)}.*)

  Lemma projected_is_fun {X Y : set} `{HX:IsProjectedSet X (Ae:=_) (Y:=X') (f:=p)} `{HY:IsProjectedSet Y (Ae:=_) (Y:=Y') (f:=q)}
    (f:X → Y) (g:X' ⇾ Y') : (∀ x, q (f x) = g (p x)) → IsFun f.
  Proof. intros H x y.
    rew [ (is_projected_set (A:=X) _ _) | (is_projected_set (A:=Y) _ _) ].
    rew [ (H x) | (H y) ].
    exact (is_fun g _ _).
  Qed.
End functions.
