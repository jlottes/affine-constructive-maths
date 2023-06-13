Require Export interfaces.subalgebra theory.groups.
Require Import sprop.
Require Import interfaces.set theory.set theory.projected_set.
Require Import logic.aprop.
Require Import easy replc rewrite_preserves.

Local Open Scope grp_scope.
Local Notation e := mon_unit.

Definition alt_Build_SubSemiGroup `{SemiGroup X} {Y:𝒫 X} :
  (∀ x y, x ∊ Y ⊠ y ∊ Y ⊸ x ∙ y ∊ Y) → SubSemiGroup Y
:= tautology.

Definition alt_Build_SubMonoid `{Monoid X} {Y:𝒫 X} :
  (∀ x y, x ∊ Y ⊠ y ∊ Y ⊸ x ∙ y ∊ Y)
 → e ∊ Y
 → SubMonoid Y
:= tautology.

Definition alt_Build_SubGroup `{Group X} {Y:𝒫 X} :
  (∀ x y, x ∊ Y ⊠ y ∊ Y ⊸ x ∙ y ∊ Y)
 → e ∊ Y
 → (∀ x, x ∊ Y ⊸ x⁻¹ ∊ Y)
 → SubGroup Y
:= tautology.

Global Hint Extern 4 (apos (_ ∙ _ ∊ _)) => simple notypeclasses refine  (andl (sub_sg_closed _ _ _) _) : typeclass_instances.
Global Hint Extern 4 (apos (e ∊ _)) => simple notypeclasses refine  (sub_mon_unit_closed _) : typeclass_instances.
Global Hint Extern 4 (apos (_⁻¹ ∊ _)) => simple notypeclasses refine  (andl (sub_grp_inv_closed _ _) _) : typeclass_instances.

Definition full_sub_sg  `{SemiGroup G} : SubSemiGroup G := tautology.
Definition full_sub_mon `{Monoid    M} : SubMonoid    M := tautology.
Definition full_sub_grp `{Group     G} : SubGroup     G := tautology.
Definition full_normal_sub_grp `{Group G} : NormalSubGroup G := tautology.
Global Hint Extern 2 (SubSemiGroup (full_subset _)) => simple notypeclasses refine full_sub_sg  : typeclass_instances.
Global Hint Extern 2 (SubMonoid    (full_subset _)) => simple notypeclasses refine full_sub_mon : typeclass_instances.
Global Hint Extern 2 (SubGroup     (full_subset _)) => simple notypeclasses refine full_sub_grp : typeclass_instances.
Global Hint Extern 2 (NormalSubGroup (full_subset _)) => simple notypeclasses refine full_normal_sub_grp : typeclass_instances.


(** Substructure predicates respect equality of subsets. *)

Lemma SubSemiGroup_proper_impl {G op} H₁ H₂
  : H₁ = H₂ → impl (@SubSemiGroup G op H₁) (SubSemiGroup H₂).
Proof. intros E P; split; try exact _. rew <-E. apply P. Qed.
Canonical Structure SubSemiGroup_fun {G op} :=
  make_weak_spred (@SubSemiGroup G op) SubSemiGroup_proper_impl.

Lemma SubMonoid_proper_impl {M op unit} N₁ N₂
  : N₁ = N₂ → impl (@SubMonoid M op unit N₁) (SubMonoid N₂).
Proof. intros E P; split; try exact _; rew <-E; apply P. Qed.
Canonical Structure SubMonoid_fun {M op unit} :=
  make_weak_spred (@SubMonoid M op unit) SubMonoid_proper_impl.

Lemma SubGroup_proper_impl {G op unit inv} H₁ H₂
  : H₁ = H₂ → impl (@SubGroup G op unit inv H₁) (SubGroup H₂).
Proof. intros E P; split; try exact _; rew <-E; apply P. Qed.
Canonical Structure SubGroup_fun {G op unit inv} :=
  make_weak_spred (@SubGroup G op unit inv) SubGroup_proper_impl.

Lemma NormalSubGroup_proper_impl {G op unit inv} H₁ H₂
  : H₁ = H₂ → impl (@NormalSubGroup G op unit inv H₁) (NormalSubGroup H₂).
Proof. intros E P; split; try exact _; rew <-E; apply P. Qed.
Canonical Structure NormalSubGroup_fun {G op unit inv} :=
  make_weak_spred (@NormalSubGroup G op unit inv) NormalSubGroup_proper_impl.

(** Induced operations on subsets when viewed as sets. *)

Definition sub_semigroup_op `{P:SemiGroup G} (H:𝒫 G) `{!SubSemiGroup H} : SgOp H.
Proof. unshelve esplit.
+ intros [x y]. exact (to_subset ((x:G) ∙ (y:G))).
+ now refine (projected_is_fun _ sg_op _).
Defined.

Definition sub_monoid_unit `{P:Monoid M} (N:𝒫 M) `{!SubMonoid N} : MonUnit N
:= to_subset (e:M).

Definition sub_group_inv `{P:Group G} (H:𝒫 G) `{!SubGroup H} : Inv H.
Proof. unshelve esplit.
+ exact (λ x, to_subset (x:G)⁻¹).
+ now refine (projected_is_fun _ inv _).
Defined.

Global Hint Extern 2 (SgOp (subset_to_set ?H)) => refine (sub_semigroup_op H) : typeclass_instances.
Global Hint Extern 2 (MonUnit (subset_to_set ?H)) => refine (sub_monoid_unit H) : typeclass_instances.
Global Hint Extern 2 (Inv (subset_to_set ?H)) => refine (sub_group_inv H) : typeclass_instances.

(** Sub structures are instances of structures when viewed as sets. *)

Lemma sub_semigroup_semigroup `{P:SemiGroup G} {H:𝒫 G} `{!SubSemiGroup H} : SemiGroup H.
Proof. intros x y z. exact (associativity (∙) (x:G) (y:G) (z:G)). Qed.
Global Hint Extern 2 (SemiGroup (subset_to_set _)) => simple notypeclasses refine sub_semigroup_semigroup : typeclass_instances.

Lemma sub_semigroup_com_semigroup `{P:CommutativeSemiGroup G} {H:𝒫 G} `{!SubSemiGroup H} : CommutativeSemiGroup H.
Proof. split; try exact _. intros x y. exact (commutativity (∙) (x:G) (y:G)). Qed.
Global Hint Extern 2 (CommutativeSemiGroup (subset_to_set _)) => simple notypeclasses refine sub_semigroup_com_semigroup : typeclass_instances.

Lemma sub_semigroup_sl `{P:SemiLattice G} {H:𝒫 G} `{!SubSemiGroup H} : SemiLattice H.
Proof. split; try exact _. intros x. exact (binary_idempotency (∙) (x:G)). Qed.
Global Hint Extern 2 (SemiLattice (subset_to_set _)) => simple notypeclasses refine sub_semigroup_sl : typeclass_instances.

Lemma sub_monoid_monoid `{P:Monoid M} {N:𝒫 M} `{!SubMonoid N} : Monoid N.
Proof. split.
+ exact _.
+ intros x. exact (left_identity (∙) (x:M)).
+ intros x. exact (right_identity (∙) (x:M)).
Qed.
Global Hint Extern 2 (Monoid (subset_to_set _)) => simple notypeclasses refine sub_monoid_monoid : typeclass_instances.

Lemma sub_monoid_com_monoid `{P:CommutativeMonoid M} {N:𝒫 M} `{!SubMonoid N} : CommutativeMonoid N.
Proof. split; try exact _. intros x y. exact (commutativity (∙) (x:M) (y:M)). Qed.
Global Hint Extern 2 (CommutativeMonoid (subset_to_set _)) => simple notypeclasses refine sub_monoid_com_monoid : typeclass_instances.

Lemma sub_monoid_bounded_sl `{P:BoundedSemiLattice M} {N:𝒫 M} `{!SubMonoid N} : BoundedSemiLattice N.
Proof. now split. Qed.
Global Hint Extern 2 (BoundedSemiLattice (subset_to_set _)) => simple notypeclasses refine sub_monoid_bounded_sl : typeclass_instances.

Lemma sub_group_group `{P:Group G} {H:𝒫 G} `{!SubGroup H} : Group H.
Proof. split.
+ exact _.
+ intros x. exact (left_inverse (∙) (x:G)).
+ intros x. exact (right_inverse (∙) (x:G)).
Qed.
Global Hint Extern 2 (Group (subset_to_set _)) => simple notypeclasses refine sub_group_group : typeclass_instances.

Lemma sub_group_abgroup `{P:AbGroup G} {H:𝒫 G} `{!SubGroup H} : AbGroup H.
Proof. split; try exact _. intros x y. exact (commutativity (∙) (x:G) (y:G)). Qed.
Global Hint Extern 2 (AbGroup (subset_to_set _)) => simple notypeclasses refine sub_group_abgroup : typeclass_instances.

Lemma sub_abgroup_normal `{P:AbGroup G} {H:𝒫 G} `{!SubGroup H} : NormalSubGroup H.
Proof. split; try exact _.
  intros x. rew <-all_adj. intros y.
  rew (commutativity (∙) y x).
  now group_simplify.
Qed.
Global Hint Extern 8 (NormalSubGroup _) => simple notypeclasses refine sub_abgroup_normal : typeclass_instances.

(** Inclusion of the substructure is structure preserving *)

Lemma from_sub_semigroup `{P:SemiGroup G} {H:𝒫 G} `{!SubSemiGroup H} : SemiGroup_Morphism (from_subset H).
Proof. split; try exact _; now intros. Qed.
Global Hint Extern 2 (SemiGroup_Morphism (from_subset _)) => simple notypeclasses refine from_sub_semigroup : typeclass_instances.

Lemma from_sub_monoid `{P:Monoid M} {N:𝒫 M} `{!SubMonoid N} : Monoid_Morphism (from_subset N).
Proof. apply alt_Build_Monoid_Morphism; now intros. Qed.
Global Hint Extern 2 (Monoid_Morphism (from_subset _)) => simple notypeclasses refine from_sub_monoid : typeclass_instances.
Global Hint Extern 2 (MonUnit_Pointed_Morphism (from_subset _)) => simple notypeclasses refine from_sub_monoid : typeclass_instances.

(** Image and preimage *)
Import image_notation.

Lemma image_sub_sg `{@SemiGroup_Morphism X Y Xop Yop f} {U:𝒫 X} `{!SubSemiGroup U} : SubSemiGroup (f⁺ U).
Proof. split; [ exact _ |]. intros y₁ y₂. unfold_image.
  rew <-aex_adj2. intros x₁ x₂. rew <-(aex_ub _ (x₁ ∙ x₂)).
  let t := constr:(tautology : ∀ P Q R S : Ω, (P ⊠ Q) ⊠ (R ⊠ S) ⊸ (P ⊠ R) ⊠ (Q ⊠ S)) in rew (t _ _ _ _).
  refine (aprod_proper_aimpl _ _).
  * now apply sub_sg_closed.
  * rewrite_preserves f. exact (is_fun (∙) (_, _) (_, _)).
Qed.
Global Hint Extern 2 (SubSemiGroup (func_op _⁺ _)) => simple notypeclasses refine image_sub_sg : typeclass_instances.

Lemma preimage_sub_sg `{@SemiGroup_Morphism X Y Xop Yop f} {U:𝒫 Y} `{!SubSemiGroup U} : SubSemiGroup (f⁻ U).
Proof. split; [ exact _ |]. intros x₁ x₂. unfold_image.
  rewrite_preserves f. now apply sub_sg_closed.
Qed.
Global Hint Extern 2 (SubSemiGroup (func_op _⁻ _)) => simple notypeclasses refine preimage_sub_sg : typeclass_instances.


Lemma image_sub_mon `{@Monoid_Morphism X Y Xop Xe Yop Ye f} {U:𝒫 X} `{!SubMonoid U} : SubMonoid (f⁺ U).
Proof. split; [ exact _ .. |]. unfold_image. exists e; split; [ exact _ | exact (preserves_unit f) ]. Qed.
Global Hint Extern 2 (SubMonoid (func_op _⁺ _)) => simple notypeclasses refine image_sub_mon : typeclass_instances.

Lemma preimage_sub_mon `{@Monoid_Morphism X Y Xop Xe Yop Ye f} {U:𝒫 Y} `{!SubMonoid U} : SubMonoid (f⁻ U).
Proof. split; [ exact _ .. |]. unfold_image. now rewrite_preserves f. Qed.
Global Hint Extern 2 (SubMonoid (func_op _⁻ _)) => simple notypeclasses refine preimage_sub_mon : typeclass_instances.


Lemma image_sub_grp `{Group X} `{Group Y} {f:X ⇾ Y} `{!SemiGroup_Morphism f} {U:𝒫 X} `{!SubGroup U} : SubGroup (f⁺ U).
Proof. split; [ exact _ ..|]. intros y. unfold_image.
  rew <-aex_adj. intros x. rew <-(aex_ub _ x⁻¹).
  refine (aprod_proper_aimpl _ _).
  * now apply sub_grp_inv_closed.
  * rewrite_preserves f. exact (is_fun inv _ _).
Qed.
Global Hint Extern 2 (SubGroup (func_op _⁺ _)) => simple notypeclasses refine image_sub_grp : typeclass_instances.

Lemma preimage_sub_grp `{Group X} `{Group Y} {f:X ⇾ Y} `{!SemiGroup_Morphism f} {U:𝒫 Y} `{!SubGroup U} : SubGroup (f⁻ U).
Proof. split; [ exact _ ..|]. intros y. unfold_image. rewrite_preserves f. now apply sub_grp_inv_closed. Qed.
Global Hint Extern 2 (SubGroup (func_op _⁻ _)) => simple notypeclasses refine preimage_sub_grp : typeclass_instances.


Lemma image_preserves_sub_sg_com `{@SemiGroup_Morphism X Y Xop Yop f} {U:𝒫 X} `{!SubSemiGroup U}
  `{!Commutative (X:=U) (∙)} : Commutative (X:=f⁺ U : 𝒫 _) (∙).
Proof. intros [y₁ ely₁][y₂ ely₂]. change (y₁ ∙ y₂ = y₂ ∙ y₁). revert ely₁ ely₂. unfold_image.
  intros [x₁[? E1]][x₂[? E2]]; rew [ <-E1 | <-E2 ]; clear y₁ y₂ E1 E2.
  rew [ <-(preserves_sg_op f _ _) | <-(preserves_sg_op f _ _) ].
  apply (is_fun f _ _).
  exact ( commutativity (∙) (to_subset x₁ : U) (to_subset x₂ : U) ).
Qed.
Global Hint Extern 2 (@Commutative (subset_to_set (func_op _⁺ _)) _ (∙)) => simple notypeclasses refine image_preserves_sub_sg_com : typeclass_instances.

Lemma preimage_preserves_sub_sg_com `{@SemiGroup_Morphism X Y Xop Yop f} {U:𝒫 Y} `{!SubSemiGroup U} `{!Injective f}
  : Commutative (X:=U) (∙) → Commutative (X:=f⁻ U : 𝒫 _) (∙).
Proof. intro. intros [x₁ elx₁][x₂ elx₂]. change (x₁ ∙ x₂ = x₂ ∙ x₁). revert elx₁ elx₂. unfold_image.
  intros ??. quote_injective f.
  exact ( commutativity (∙) (to_subset (f x₁) : U) (to_subset (f x₂) : U) ).
Qed.

Lemma image_com_sg `{@SemiGroup_Morphism X Y Xop Yop f} {U:𝒫 X} `{!SubSemiGroup U} `{!CommutativeSemiGroup U}
  : CommutativeSemiGroup (subset_to_set (f⁺ U )).
Proof. now split. Qed.

Lemma image_com_mon `{@Monoid_Morphism X Y Xop Xe Yop Ye f} {U:𝒫 X} `{!SubMonoid U} `{!CommutativeMonoid U}
  : CommutativeMonoid (subset_to_set (f⁺ U)).
Proof. now split. Qed.

Lemma image_abgrp `{Group X} `{Group Y} (f:X ⇾ Y) `{!SemiGroup_Morphism f} {U:𝒫 X} `{!SubGroup U} `{!AbGroup U}
  : AbGroup (subset_to_set (f⁺ U)).
Proof. now split. Qed.

Global Hint Extern 2 (CommutativeSemiGroup (subset_to_set (func_op _⁺ _))) => simple notypeclasses refine image_com_sg : typeclass_instances.
Global Hint Extern 2 (CommutativeMonoid (subset_to_set (func_op _⁺ _))) => simple notypeclasses refine image_com_mon : typeclass_instances.
Global Hint Extern 2 (AbGroup (subset_to_set (func_op _⁺ _))) => simple notypeclasses refine image_abgrp : typeclass_instances.

(** Quotient Group *)

Definition QuotientGroup G {op u i} H {P:@NormalSubGroup G op u i H} := set_T G.
Local Notation "G / H" := (QuotientGroup G H) (at level 40) : type_scope.

Definition QuotientGroup_equiv `{P:NormalSubGroup (G:=G) H}  : Equiv (G/H)
  := λ x y, x ∙ y⁻¹ ∊ H.
Global Hint Extern 1 (Equiv (_ / _)) => refine QuotientGroup_equiv : typeclass_instances.

Lemma QuotientGroup_equiv_subrel `{P:NormalSubGroup (G:=G) H} : Subrelation (@equiv G _) (@equiv (G/H) _).
Proof. intros x y. change (x = y ⊸ x ∙ y⁻¹ ∊ H).
  rew exact:(is_fun (∙ y⁻¹) x y : x = y ⊸ x ∙ y⁻¹ = y ∙ y⁻¹). group_simplify.
  rew <-(equal_element H e _), (aprod_true_r (_ : e ∊ H)).
  now apply symmetry.
Qed.

Lemma QuotientGroup_is_set `{P:NormalSubGroup (G:=G) H} : IsSet (G/H).
Proof. split.
+ intros x. change (x ∙ x⁻¹ ∊ H). now group_simplify.
+ intros x y. change (x ∙ y⁻¹ ∊ H ⊸ y ∙ x⁻¹ ∊ H).
  rew (inverse_swap_r y x). exact (sub_grp_inv_closed _ _).
+ intros x y z. change (x ∙ y⁻¹ ∊ H ⊠ y ∙ z⁻¹ ∊ H ⊸ x ∙ z⁻¹ ∊ H).
  replc (x ∙ z⁻¹) with ( (x ∙ y⁻¹) ∙ (y ∙ z⁻¹) ) by now group_simplify.
  exact (sub_sg_closed _ _ _).
Qed.
Global Hint Extern 1 (IsSet (_ / _)) => simple notypeclasses refine QuotientGroup_is_set : typeclass_instances.

Canonical Structure QuotientGroup_set G {op u i} H {P:@NormalSubGroup G op u i H}  := set_make (G/H).
Local Notation "G / H" := (QuotientGroup_set G H) (at level 40, only printing).

Global Hint Extern 1 (MonUnit (QuotientGroup_set _ (u:=?u) _)) => refine u : typeclass_instances.

Lemma QuotientGroup_op_is_fun `{P:NormalSubGroup (G:=G) H}  : @IsFun ((G/H) ⊗ (G/H)) (G/H) (@sg_op G _).
Proof. intros [x₁ y₁][x₂ y₂]. change (set_T G) in x₁, y₁, x₂, y₂.
  change (x₁ ∙ x₂⁻¹ ∊ H ⊠ y₁ ∙ y₂⁻¹ ∊ H ⊸ (x₁ ∙ y₁) ∙ (x₂ ∙ y₂)⁻¹ ∊ H).
  replc ( (x₁ ∙ y₁) ∙ (x₂ ∙ y₂)⁻¹ ) with ( (x₁ ∙ x₂⁻¹) ∙  (x₂ ∙ (y₁ ∙ y₂⁻¹) ∙ x₂⁻¹) ) by now group_simplify.
  rew (normality H (y₁ ∙ y₂⁻¹)), (all_lb _ x₂).
  exact (sub_sg_closed _ _ _).
Qed.

Lemma QuotientGroup_inv_is_fun `{P:NormalSubGroup (G:=G) H} : @IsFun (G/H) (G/H) (@inv G _).
Proof. intros x y. change (set_T G) in x, y.
  change (x ∙ y⁻¹ ∊ H ⊸ x⁻¹ ∙ (y⁻¹)⁻¹ ∊ H).
  replc ( x⁻¹ ∙ (y⁻¹)⁻¹ ) with ( y⁻¹ ∙ (x ∙ y⁻¹)⁻¹ ∙ (y⁻¹)⁻¹ ) by now group_simplify.
  rew (sub_grp_inv_closed H _), (normality H (x ∙ y⁻¹)⁻¹).
  exact (all_lb _ _).
Qed.

Definition QuotientGroup_op  G {op unit inv} H {P} : SgOp (G/H) := @make_fun _ _ _ (@QuotientGroup_op_is_fun  G op unit inv H P).
Definition QuotientGroup_inv G {op unit inv} H {P} : Inv  (G/H) := @make_fun _ _ _ (@QuotientGroup_inv_is_fun G op unit inv H P).
Global Hint Extern 1 (SgOp (QuotientGroup_set ?G ?H)) => refine (QuotientGroup_op  G H) : typeclass_instances.
Global Hint Extern 1 (Inv  (QuotientGroup_set ?G ?H)) => refine (QuotientGroup_inv G H) : typeclass_instances.

Lemma QuotientGroup_Group `{P:NormalSubGroup (G:=G) H} : Group (G/H) .
Proof. apply alt_Build_Group; [ intros x y z | intros x .. ]; apply (QuotientGroup_equiv_subrel _ _).
+ exact (associativity  (∙) (x:G) (y:G) (z:G)).
+ exact (left_identity  (∙) (x:G)).
+ exact (right_identity (∙) (x:G)).
+ exact (left_inverse   (∙) (x:G)).
+ exact (right_inverse  (∙) (x:G)).
Qed.

