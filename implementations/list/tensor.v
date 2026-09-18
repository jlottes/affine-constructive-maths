Require Import interfaces.set abstract_algebra bundled_algebra interfaces.free_monoid.
Require Import interfaces.sprop theory.set theory.groups.
Require Import logic.aprop.
Require Export list.base.
Require Import easy rewrite tactics.misc simplify.
Require Import set_lambda.

Local Open Scope sg_op_scope.

Definition tensor_list X := list X.
Global Hint Extern 1 (Equiv (tensor_list _)) => refine (list_equiv aprod) : typeclass_instances.

Local Instance tensor_list_is_set X : IsSet (tensor_list X).
Proof. split; hnf; unfold equiv.
+ induction x as [|x₀ x]; now simpl.
+ induction x as [|x₀ x]; intros [|y₀ y]; try now simpl.
  change list with tensor_list in *.
  change (x₀ = y₀ ⊠ x = y ⊸ y₀ = x₀ ⊠ y = x).
  refine (aprod_proper_aimpl _ (IHx y)).
  now apply symmetry.
+ induction x as [|x₀ x]; intros [|y₀ y][|z₀ z]; try now simpl.
  change list with tensor_list in *.
  change ((x₀ = y₀ ⊠ x = y) ⊠ (y₀ = z₀ ⊠ y = z) ⊸ (x₀ = z₀ ⊠ x = z)).
  rew (aprod_assoc _ _ _). rew <-(aprod_assoc (x=y) _ _). rew (aprod_com (x=y) _).
  rew (aprod_assoc _ _ _). rew <-(aprod_assoc (x₀=y₀) _ _).
  refine (aprod_proper_aimpl _ (IHx y z)).
  now apply transitivity.
Qed.

Canonical Structure TensorList X := set_make (tensor_list X).
Local Notation "X *" := (TensorList X) (at level 1, left associativity, format "X *").

Global Hint Extern 1 (MonUnit _*) => refine nil : typeclass_instances.
Local Abbreviation ε := (mon_unit (M:=_*)).

Lemma TensorList_cons_is_fun X : @IsFun (X ⊗ X*) X* (λ p, cons (proj1 p) (proj2 p)).
Proof. now intros [x₀ x][y₀ y]. Qed.
Definition TensorCons {X} : X ⊗ X* ⇾ X* := @func_make _ _ _ (TensorList_cons_is_fun X).
Local Notation "x :: y" := (func_op TensorCons (x, y)) (at level 60, right associativity).

Definition TensorList_unit {X} : X ⇾ X* := ap2 TensorCons ε.
Local Abbreviation η := TensorList_unit.
Local Notation "[ x ]" := (func_op η x).
Global Hint Extern 1 (Cast ?X (?X *)) => refine TensorList_unit : typeclass_instances.

Definition TensorList_induction {X} (P : X* → Ω) : (∏ x₀ x, P x ⊸ P (x₀ :: x)) → (P ε ⊸ all P) := list_induction P.
Definition TensorList_sinduction {X} (P:X* → SProp) : P ε → (∀ x₀ x, P x → P (x₀ :: x)) → ∀ x, P x := list_sinduction P.

Local Ltac doit P := let x₀ := fresh "x₀" in let x := fresh "x" in let IHx := fresh "IHx" in
  let y₀ := fresh "y₀" in let y := fresh "y" in
  hnf; intros [x y]; revert x y; refine (TensorList_sinduction _ _ _);
  [| intros x₀ x IHx]; intros [|y₀ y];
  [ now change (P 𝐓) | now change (P 𝐅) .. |
    specialize (IHx y); now change (P (x₀ = y₀ ⊠ x = y)) ].
Lemma TensorList_DecidableEquality   `{!DecidableEquality   X} : DecidableEquality   X*.  Proof. doit Decidable.   Qed.
Lemma TensorList_AffirmativeEquality `{!AffirmativeEquality X} : AffirmativeEquality X*.  Proof. doit Affirmative. Qed.
Lemma TensorList_RefutativeEquality  `{!RefutativeEquality  X} : RefutativeEquality  X*.  Proof. doit Refutative.  Qed.
Global Hint Extern 2 (DecidableEquality   _*) => simple notypeclasses refine TensorList_DecidableEquality   : typeclass_instances.
Global Hint Extern 2 (AffirmativeEquality _*) => simple notypeclasses refine TensorList_AffirmativeEquality : typeclass_instances.
Global Hint Extern 2 (RefutativeEquality  _*) => simple notypeclasses refine TensorList_RefutativeEquality  : typeclass_instances.

Import projection_notation.

Local Instance TensorList_match_is_fun@{u} {X Y:set@{u}} : @IsFun (Y × ((X ⊗ X* ) ⇾ Y) ⊗ X* ) Y
   (λ p, match π₂ p with
         | nil => π₁ (π₁ p)
         | cons x l => π₂ (π₁ p) (x, l)
         end).
Proof. intros [p [|x l]][q [|y l']].
+ change (p = q ⊠ atrue ⊸ π₁ p = π₁ q).
  rew (aprod_unit_r _). exact (is_fun (prod_proj1 _ _) _ _).
+ change (?P ⊸ ?Q) with (p = q ⊠ afalse ⊸ Q). now rew (aprod_false_r _).
+ change (?P ⊸ ?Q) with (p = q ⊠ afalse ⊸ Q). now rew (aprod_false_r _).
+ let f := constr:( set:( (λ '((y, f), q) : (Y × (X ⊗ X* ⇾ Y)) ⊗ (X ⊗ X*), f q) ) ) in
  exact ( is_fun f (p, (x, l)) (q, (y, l')) ).
Qed.
Definition TensorList_match {X Y} := curry (@func_make _ _ _ (@TensorList_match_is_fun X Y)).


Section fold_right.
  Local Instance fold_right_is_fun@{u} {X Y:set@{u}} (f: X ⊗ Y ⇾ Y) : @IsFun (X* ⊗ Y) Y (λ '(xs, y), fold_right f xs y).
  Proof. intros [x y₀][x' y₀']. unfold proj1, proj2. unfold_pair_eq.
    revert x x'. refine (TensorList_sinduction _ _ _).
  + intros [|x₀ x'].
    * now change (ε = ε :> X* ⊠ y₀ = y₀' ⊸ y₀ = y₀').
    * change (ε = cons x₀ x') with afalse. now simplify.
  + intros x₀ x IH [|x₀' x'].
    * change (x₀ :: x = nil) with afalse. now simplify.
    * change ( (x₀ = x₀' ⊠ x = x') ⊠ y₀ = y₀' ⊸ f (x₀, fold_right f x y₀) = f (x₀', fold_right f x' y₀') ).
      rew [(aprod_assoc _ _ _) | <- (is_fun f _ _)].
      refine (aprod_proper_aimpl _ _); [ refl | exact (IH _) ].
  Qed.

  Definition TensorList_fold_right {X Y} (f: X ⊗ Y ⇾ Y) : X* ⊗ Y ⇾ Y := @func_make _ _ _ (fold_right_is_fun f).
End fold_right.

Definition TensorList_concat {X} : X* ⊗ X* ⇾ X* := TensorList_fold_right TensorCons.
Global Hint Extern 1 (SgOp _*) => refine (TensorList_concat) : typeclass_instances.

Definition TensorList_induction_alt `(P:X* → Ω) : (∏ x₀ x, P x ⊸ P ([x₀] ∙ x)) → (P ε ⊸ all P)
:= TensorList_induction P.
Definition TensorList_sinduction_alt `(P:X* → SProp) : P ε → (∀ x₀ x, P x → P ([x₀] ∙ x)) → ∀ x, P x
:= TensorList_sinduction P.

Lemma TensorList_sdestruct `(P:X* → SProp) : P ε → (∀ x₀ x, P ([x₀] ∙ x)) → ∀ x, P x.
Proof. intros P0 Ps [|??]; trivial. exact (Ps _ _). Qed.

Local Instance TensorList_concat_assoc X: Associative (X:=X*) (∙).
Proof. refine (TensorList_sinduction_alt _ _ _); [ easy | intros x₀ x IHx ].
  intros y z. change ( [x₀] ∙ (x ∙ (y ∙ z)) = [x₀] ∙ (x ∙ y ∙ z) ).
  now rew (IHx y z).
Qed.

Local Instance TensorList_concat_left_id X: LeftIdentity (X:=X*) (∙) ε.
Proof. now hnf. Qed.

Local Instance TensorList_concat_right_id X: RightIdentity (X:=X*) (∙) ε.
Proof. refine (TensorList_sinduction_alt _ _ _); [ easy | intros x₀ x IHx ].
  change ([x₀] ∙ (x ∙ ε) = [x₀] ∙ x). now rew IHx.
Qed.

Local Instance TensorList_is_monoid {X} : Monoid X*.
Proof. now apply alt_Build_Monoid. Qed.
Global Hint Extern 2 (Monoid _*) => simple notypeclasses refine TensorList_is_monoid : typeclass_instances.
Global Hint Extern 2 (SemiGroup _*) => simple notypeclasses refine TensorList_is_monoid : typeclass_instances.

Canonical Structure TensorList_mon X := make_monoid X*.

Global Hint Extern 1 (Cast ?X (monoid_car (TensorList_mon ?X))) => refine TensorList_unit : typeclass_instances.

(*
Require Import free_groups.

Definition from_tensor_list {X} : FromFreeMonoid (X:=X) η
  := λ Y oY uY f, set:(λ x, TensorList_fold_right (uncurry set:(λ x y, f x ∙ y)) (x, mon_unit)).
Global Hint Extern 1 (FromFreeMonoid η) => refine from_tensor_list : typeclass_instances.

Section free_monoid.
  Context {X} `{Monoid Y} (f:X ⇾ Y).
  Notation e := (@mon_unit Y _).
  Notation f' := (from_free_monoid η f).

  Lemma from_tensor_list_mor : Monoid_Morphism f'.
  Proof. apply alt_Build_Monoid_Morphism; [| refl].
    refine (TensorList_sinduction_alt _ _ _); [| intros a x IH ]; intros y.
  + change (f' ε) with e; now simplify.
  + change (f a ∙ f' (x ∙ y) = (f a ∙ f' x) ∙ f' y).
    rew (IH y). now apply associativity.
  Qed.
  Let inst : Monoid_Morphism f'.  Proof from_tensor_list_mor.

  Lemma from_tensor_list_ext : f' ∘ η = f.
  Proof. intros x. change (f x ∙ e = f x). now simplify. Qed.

  Context (h : X* ⇾ Y) `{!Monoid_Morphism h}.

  Lemma from_tensor_list_unique : h ∘ η = f → h = f'.
  Proof. intros E. refine (TensorList_sinduction_alt _ _ _).
  + now rew [ (preserves_unit h) | (preserves_unit f') ].
  + intros x xs IH. rew [ (preserves_sg_op h _ _) | (preserves_sg_op f' _ _) ].
    rew IH. rew <-exact:(simplify_thm (is_fun (∙ f' xs) (h [x]) (f' [x]))).
    change ( (h ∘ η) x = f x ∙ e ). rew E. now simplify.
  Qed.
End free_monoid.

Lemma tensor_list_free_mon {X} : FreeMonoid (X:=X) η.
Proof. split; try exact _; intros ???? f.
+ apply from_tensor_list_mor.
+ apply from_tensor_list_ext.
+ apply from_tensor_list_unique.
Qed.
*)


Section to_monoid.
  Universes u.
  Context {X:set@{u}} {M:monoid@{u}} (f:X ⇾ M).
  Abbreviation e := (mon_unit (M:=monoid_car M)).

  Definition TensorList_to_monoid : X* ⇾ M := set:(λ x, TensorList_fold_right (set:(λ '(x, y), f x ∙ y)) (x, e)).
  Local Abbreviation g := TensorList_to_monoid.

  Lemma TensorList_to_monoid_is_mon_mor : Monoid_Morphism g.
  Proof. apply alt_Build_Monoid_Morphism; [| refl].
    refine (TensorList_sinduction_alt _ _ _); [| intros a x IH ]; intros y.
  + change (g y = e ∙ g y). now simplify.
  + change (f a ∙ g (x ∙ y) = (f a ∙ g x) ∙ g y).
    rew (IH y). now group_simplify.
  Qed.
  Definition TensorList_to_monoid_mon_mor := @make_monoid_morphism _ _ g TensorList_to_monoid_is_mon_mor.

  Lemma TensorList_to_monoid_spec : f = g ∘ η.
  Proof. intros a. change (f a = f a ∙ e). now simplify. Qed.

  Local Notation "X ⟶ Y" := (monoid_morphism X Y).
  Lemma TensorList_to_monoid_unique (h:X* ⟶ M) : f = h ∘ η → h = g :> (X* ⇾ M).
  Proof. pose proof TensorList_to_monoid_is_mon_mor.
    intros E. refine (TensorList_sinduction_alt _ _ _).
  + now rew (preserves_unit _).
  + intros x₀ x IH. rew (preserves_sg_op _ _ _).
    now rew [ IH | <-(E x₀ : f x₀ = h (η x₀)) | <-(TensorList_to_monoid_spec x₀ : f x₀ = g (η x₀)) ].
  Qed.
End to_monoid.
Canonical TensorList_to_monoid_mon_mor.

Global Hint Extern 1 (FromFreeMonoid (cast ?X (monoid_car (TensorList_mon ?X)))) => refine (@TensorList_to_monoid _) : typeclass_instances.
Global Hint Extern 1 (FromFreeMonoid (cast ?X (TensorList ?X))) => refine (@TensorList_to_monoid _) : typeclass_instances.
Global Hint Extern 1 (FromFreeMonoid TensorList_unit) => refine (@TensorList_to_monoid _) : typeclass_instances.

Lemma TensorList_FreeMonoid {X} : FreeMonoid (X:=X) η.
Proof. split; intros M f.
+ apply TensorList_to_monoid_spec.
+ apply TensorList_to_monoid_unique.
Qed.
Global Hint Extern 2 (FreeMonoid (cast ?X (monoid_car (TensorList ?X)))) => refine TensorList_FreeMonoid : typeclass_instances.
Global Hint Extern 2 (FreeMonoid (cast ?X (TensorList ?X))) => refine TensorList_FreeMonoid : typeclass_instances.
Global Hint Extern 2 (FreeMonoid TensorList_unit) => refine TensorList_FreeMonoid : typeclass_instances.

Definition TensorList_map@{u} {X Y:set@{u}} (f:X ⇾ Y) := TensorList_to_monoid_mon_mor (TensorList_unit ∘ f).

