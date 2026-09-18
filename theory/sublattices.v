Require Export interfaces.subalgebra theory.lattices theory.subgroups.
Require Import sprop.
Require Import interfaces.set theory.set theory.projected_set.
Require Import logic.aprop.
Require Import easy replc rewrite_preserves.

Definition alt_Build_MeetSubSemiLattice : ∀ `{MeetSemiLattice L} {U:𝒫 L},
  (∀ x y, x ∊ U ⊠ y ∊ U ⊸ x ⊓ y ∊ U) → MeetSubSemiLattice U
:= @alt_Build_SubSemiGroup.

Definition alt_Build_JoinSubSemiLattice : ∀ `{JoinSemiLattice L} {U:𝒫 L},
  (∀ x y, x ∊ U ⊠ y ∊ U ⊸ x ⊔ y ∊ U) → JoinSubSemiLattice U
:= @alt_Build_SubSemiGroup.

Definition alt_Build_MeetSubBoundedSemiLattice : ∀ `{BoundedMeetSemiLattice L} {U:𝒫 L},
  (∀ x y, x ∊ U ⊠ y ∊ U ⊸ x ⊓ y ∊ U)
 → ⊤ ∊ U
 → MeetSubBoundedSemiLattice U
:= @alt_Build_SubMonoid.

Definition alt_Build_JoinSubBoundedSemiLattice : ∀ `{BoundedJoinSemiLattice L} {U:𝒫 L},
  (∀ x y, x ∊ U ⊠ y ∊ U ⊸ x ⊔ y ∊ U)
 → ⊥ ∊ U
 → JoinSubBoundedSemiLattice U
:= @alt_Build_SubMonoid.


Global Hint Extern 4 (apos (_ ⊓ _ ∊ _)) => simple notypeclasses refine (andl (sub_meet_closed _ _) _) : typeclass_instances.
Global Hint Extern 4 (apos (_ ⊔ _ ∊ _)) => simple notypeclasses refine (andl (sub_join_closed _ _) _) : typeclass_instances.
Global Hint Extern 4 (apos (⊤ ∊ _)) => simple notypeclasses refine sub_top_closed : typeclass_instances.
Global Hint Extern 4 (apos (⊥ ∊ _)) => simple notypeclasses refine sub_bot_closed : typeclass_instances.

Definition full_meet_sub_sl  : ∀ `{MeetSemiLattice L}, MeetSubSemiLattice (full_subset L) := @full_sub_sg.
Definition full_meet_sub_bsl : ∀ `{BoundedMeetSemiLattice L}, MeetSubBoundedSemiLattice (full_subset L) := @full_sub_mon.
Definition full_join_sub_sl  : ∀ `{JoinSemiLattice L}, JoinSubSemiLattice (full_subset L) := @full_sub_sg.
Definition full_join_sub_bsl : ∀ `{BoundedJoinSemiLattice L}, JoinSubBoundedSemiLattice (full_subset L) := @full_sub_mon.

Global Hint Extern 2 (MeetSubSemiLattice (full_subset _)) => simple notypeclasses refine full_meet_sub_sl : typeclass_instances.
Global Hint Extern 2 (MeetSubBoundedSemiLattice (full_subset _)) => simple notypeclasses refine full_meet_sub_bsl : typeclass_instances.
Global Hint Extern 2 (JoinSubSemiLattice (full_subset _)) => simple notypeclasses refine full_join_sub_sl : typeclass_instances.
Global Hint Extern 2 (JoinSubBoundedSemiLattice (full_subset _)) => simple notypeclasses refine full_join_sub_bsl : typeclass_instances.


(** Substructure predicates respect equality of subsets. *)

Canonical Structure MeetSubSemiLattice_fun {L m} :=
  make_fun_alt (@MeetSubSemiLattice L m) (@SubSemiGroup_fun L m).

Canonical Structure MeetSubBoundedSemiLattice_fun {L m t} :=
  make_fun_alt (@MeetSubBoundedSemiLattice L m t) (@SubMonoid_fun L m t).

Canonical Structure JoinSubSemiLattice_fun {L j} :=
  make_fun_alt (@JoinSubSemiLattice L j) (@SubSemiGroup_fun L j).

Canonical Structure JoinSubBoundedSemiLattice_fun {L j b} :=
  make_fun_alt (@JoinSubBoundedSemiLattice L j b) (@SubMonoid_fun L j b).

(** Induced operations on subsets when viewed as sets. *)

Definition sub_meet_sl_meet@{u} : ∀ `{@MeetSubSemiLattice@{u} L m U}, Meet U := @sub_semigroup_op.
Definition sub_join_sl_join@{u} : ∀ `{@JoinSubSemiLattice@{u} L j U}, Join U := @sub_semigroup_op.

Definition sub_meet_bsl_top@{u} : ∀ `{@MeetSubBoundedSemiLattice@{u} L m t U}, Top U := @sub_monoid_unit.
Definition sub_join_bsl_bot@{u} : ∀ `{@JoinSubBoundedSemiLattice@{u} L j b U}, Bottom U := @sub_monoid_unit.

Arguments sub_meet_sl_meet {L m} U {_}.
Arguments sub_join_sl_join {L j} U {_}.
Arguments sub_meet_bsl_top {L m t} U {_}.
Arguments sub_join_bsl_bot {L j b} U {_}.

Global Hint Extern 2 (Meet (subset_to_set ?U)) => refine (sub_meet_sl_meet U) : typeclass_instances.
Global Hint Extern 2 (Join (subset_to_set ?U)) => refine (sub_join_sl_join U) : typeclass_instances.
Global Hint Extern 2 (Top    (subset_to_set ?U)) => refine (sub_meet_bsl_top U) : typeclass_instances.
Global Hint Extern 2 (Bottom (subset_to_set ?U)) => refine (sub_join_bsl_bot U) : typeclass_instances.

(** Sub structures are instances of structures when viewed as sets. *)

Definition sub_meet_sl@{u} : ∀ {L:set@{u}} `{P:MeetSemiLattice L} {U:𝒫 L} `{!MeetSubSemiLattice U}, MeetSemiLattice U := @sub_semigroup_sl.
Definition sub_meet_bsl@{u} : ∀ {L:set@{u}} `{P:BoundedMeetSemiLattice L} {U:𝒫 L} `{!MeetSubBoundedSemiLattice U}, BoundedMeetSemiLattice U := @sub_monoid_bounded_sl.
Definition sub_join_sl@{u} : ∀ {L:set@{u}} `{P:JoinSemiLattice L} {U:𝒫 L} `{!JoinSubSemiLattice U}, JoinSemiLattice U := @sub_semigroup_sl.
Definition sub_join_bsl@{u} : ∀ {L:set@{u}} `{P:BoundedJoinSemiLattice L} {U:𝒫 L} `{!JoinSubBoundedSemiLattice U}, BoundedJoinSemiLattice U := @sub_monoid_bounded_sl.

Global Hint Extern 2 (MeetSemiLattice (subset_to_set _)) => simple notypeclasses refine sub_meet_sl : typeclass_instances.
Global Hint Extern 2 (BoundedMeetSemiLattice (subset_to_set _)) => simple notypeclasses refine sub_meet_bsl : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice (subset_to_set _)) => simple notypeclasses refine sub_join_sl : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice (subset_to_set _)) => simple notypeclasses refine sub_join_bsl : typeclass_instances.

(** Inclusion of the substructure is structure preserving *)

Definition from_meet_sub_sl : ∀ `{@MeetSubSemiLattice L m U}, MeetSemiLattice_Morphism (from_subset U) := @from_sub_semigroup.
Definition from_join_sub_sl : ∀ `{@JoinSubSemiLattice L j U}, JoinSemiLattice_Morphism (from_subset U) := @from_sub_semigroup.
Global Hint Extern 2 (MeetSemiLattice_Morphism (from_subset _)) => simple notypeclasses refine from_meet_sub_sl : typeclass_instances.
Global Hint Extern 2 (JoinSemiLattice_Morphism (from_subset _)) => simple notypeclasses refine from_join_sub_sl : typeclass_instances.

Definition from_meet_sub_bsl : ∀ `{@MeetSubBoundedSemiLattice L m t U}, BoundedMeetSemiLattice_Morphism (from_subset U) := @from_sub_monoid.
Definition from_join_sub_bsl : ∀ `{@JoinSubBoundedSemiLattice L j b U}, BoundedJoinSemiLattice_Morphism (from_subset U) := @from_sub_monoid.
Global Hint Extern 2 (BoundedMeetSemiLattice_Morphism (from_subset _)) => simple notypeclasses refine from_meet_sub_bsl : typeclass_instances.
Global Hint Extern 2 (BoundedJoinSemiLattice_Morphism (from_subset _)) => simple notypeclasses refine from_join_sub_bsl : typeclass_instances.

(** Sublattices *)

Lemma alt_Build_SubLattice `{P:@Lattice L m j} (U : 𝒫 L) : MeetSubSemiLattice U → JoinSubSemiLattice U → SubLattice U.
Proof. intros; now split. Qed.

Lemma alt_Build_SubLattice2 `{P:@Lattice L m j} (U : 𝒫 L) :
  (∀ x y, x ∊ U ⊠ y ∊ U ⊸ x ⊓ y ∊ U)
 → (∀ x y, x ∊ U ⊠ y ∊ U ⊸ x ⊔ y ∊ U)
 → SubLattice U.
Proof. intros; apply alt_Build_SubLattice; [ now apply alt_Build_MeetSubSemiLattice | now apply alt_Build_JoinSubSemiLattice ]. Qed.

Definition full_sub_lattice : ∀ `{Lattice L}, SubLattice (full_subset L).  Proof. intros; now split. Qed.
Global Hint Extern 2 (SubLattice (full_subset _)) => simple notypeclasses refine full_sub_lattice : typeclass_instances.

(** Substructure predicates respect equality of subsets. *)

Lemma SubLattice_proper_impl {L m j} U₁ U₂
  : U₁ = U₂ → impl (@SubLattice L m j U₁, SubLattice U₂).
Proof. intros E P; split; try exact _; now rew <-E. Qed.
Canonical Structure SubLattice_fun {L m j} :=
  make_weak_spred (@SubLattice L m j) SubLattice_proper_impl.

(** Sub structures are instances of structures when viewed as sets. *)
Lemma sub_lattice_lattice `{@SubLattice L m j U} : Lattice U.
Proof. split; try exact _.
+ intros x y. exact (join_meet_absorption (x:L) (y:L)).
+ intros x y. exact (meet_join_absorption (x:L) (y:L)).
Qed.
Global Hint Extern 2 (Lattice (subset_to_set _)) => simple notypeclasses refine sub_lattice_lattice : typeclass_instances.

Lemma sub_lattice_distr_lattice `{@DistributiveLattice L m j} {U:𝒫 L} `{!SubLattice U} : DistributiveLattice U.
Proof. split; try exact _.
+ intros x y z. exact (join_meet_distr_l (x:L) (y:L) (z:L)).
+ intros x y z. exact (meet_join_distr_l (x:L) (y:L) (z:L)).
Qed.
Global Hint Extern 2 (DistributiveLattice (subset_to_set _)) => simple notypeclasses refine sub_lattice_distr_lattice : typeclass_instances.

(** Inclusion of the substructure is structure preserving *)

Lemma from_sub_lattice `{@SubLattice L m j U} : Lattice_Morphism (from_subset U).
Proof. now split. Qed.
Global Hint Extern 2 (Lattice_Morphism (from_subset _)) => simple notypeclasses refine from_sub_lattice : typeclass_instances.

(** Image and preimage *)
Import image_notation.

Definition image_meet_sub_sl@{u} : ∀ {X Y:set@{u}} `{@MeetSemiLattice_Morphism X Y mX mY f} {U:𝒫 X} `{!MeetSubSemiLattice U}, MeetSubSemiLattice (f⁎ U) := @image_sub_sg.
Definition image_join_sub_sl@{u} : ∀ {X Y:set@{u}} `{@JoinSemiLattice_Morphism X Y jX jY f} {U:𝒫 X} `{!JoinSubSemiLattice U}, JoinSubSemiLattice (f⁎ U) := @image_sub_sg.
Global Hint Extern 2 (MeetSubSemiLattice (func_op _⁎ _)) => simple notypeclasses refine image_meet_sub_sl : typeclass_instances.
Global Hint Extern 2 (JoinSubSemiLattice (func_op _⁎ _)) => simple notypeclasses refine image_join_sub_sl : typeclass_instances.

Definition preimage_meet_sub_sl@{u} : ∀ {X Y:set@{u}} `{@MeetSemiLattice_Morphism X Y mX mY f} {U:𝒫 Y} `{!MeetSubSemiLattice U}, MeetSubSemiLattice (f* U) := @preimage_sub_sg.
Definition preimage_join_sub_sl@{u} : ∀ {X Y:set@{u}} `{@JoinSemiLattice_Morphism X Y jX jY f} {U:𝒫 Y} `{!JoinSubSemiLattice U}, JoinSubSemiLattice (f* U) := @preimage_sub_sg.
Global Hint Extern 2 (MeetSubSemiLattice (func_op _* _)) => simple notypeclasses refine preimage_meet_sub_sl : typeclass_instances.
Global Hint Extern 2 (JoinSubSemiLattice (func_op _* _)) => simple notypeclasses refine preimage_join_sub_sl : typeclass_instances.

Definition image_meet_sub_bsl@{u} : ∀ {X Y:set@{u}} `{@BoundedMeetSemiLattice_Morphism X Y mX tX mY tY f} {U:𝒫 X} `{!MeetSubBoundedSemiLattice U}, MeetSubBoundedSemiLattice (f⁎ U) := @image_sub_mon.
Definition image_join_sub_bsl@{u} : ∀ {X Y:set@{u}} `{@BoundedJoinSemiLattice_Morphism X Y jX bX jY bY f} {U:𝒫 X} `{!JoinSubBoundedSemiLattice U}, JoinSubBoundedSemiLattice (f⁎ U) := @image_sub_mon.
Global Hint Extern 2 (MeetSubBoundedSemiLattice (func_op _⁎ _)) => simple notypeclasses refine image_meet_sub_bsl : typeclass_instances.
Global Hint Extern 2 (JoinSubBoundedSemiLattice (func_op _⁎ _)) => simple notypeclasses refine image_join_sub_bsl : typeclass_instances.

Definition preimage_meet_sub_bsl@{u} : ∀ {X Y:set@{u}} `{@BoundedMeetSemiLattice_Morphism X Y mX tX mY tY f} {U:𝒫 Y} `{!MeetSubBoundedSemiLattice U}, MeetSubBoundedSemiLattice (f* U) := @preimage_sub_mon.
Definition preimage_join_sub_bsl@{u} : ∀ {X Y:set@{u}} `{@BoundedJoinSemiLattice_Morphism X Y jX bX jY bY f} {U:𝒫 Y} `{!JoinSubBoundedSemiLattice U}, JoinSubBoundedSemiLattice (f* U) := @preimage_sub_mon.
Global Hint Extern 2 (MeetSubBoundedSemiLattice (func_op _* _)) => simple notypeclasses refine preimage_meet_sub_bsl : typeclass_instances.
Global Hint Extern 2 (JoinSubBoundedSemiLattice (func_op _* _)) => simple notypeclasses refine preimage_join_sub_bsl : typeclass_instances.

Lemma image_sub_lattice `{@Lattice_Morphism X Y mX jX mY jY f} {U:𝒫 X} `{!SubLattice U, !Lattice Y} : SubLattice (f⁎ U).  Proof. now split. Qed.
Lemma preimage_sub_lattice `{@Lattice_Morphism X Y mX jX mY jY f} {U:𝒫 Y} `{!SubLattice U, !Lattice X} : SubLattice (f* U).  Proof. now split. Qed.
Global Hint Extern 2 (SubLattice (func_op _⁎ _)) => simple notypeclasses refine image_sub_lattice : typeclass_instances.
Global Hint Extern 2 (SubLattice (func_op _* _)) => simple notypeclasses refine preimage_sub_lattice : typeclass_instances.

Lemma image_sub_lattice_lattice@{u} {X Y:set@{u}} `{@SubLattice X mX jX U} `{!Lattice U} `{@Lattice Y mY jY} {f:X ⇾ Y} `{!Lattice_Morphism f} : Lattice (subset_to_set (f⁎ U)).
Proof. now split. Qed.
Global Hint Extern 2 (Lattice (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_sub_lattice_lattice : typeclass_instances.

Lemma image_sub_lattice_distr_lattice@{u} {X Y:set@{u}} `{@SubLattice X mX jX U} `{!DistributiveLattice U} `{@Lattice Y mY jY} {f:X ⇾ Y} `{!Lattice_Morphism f} : DistributiveLattice (subset_to_set (f⁎ U)).
Proof. split; try exact _.
+ intros [x elx][y ely][z elz]. change (x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)). revert elx ely elz. unfold_image.
  intros [a[Ex ela]][b[Ey elb]][c[Ez elc]]. rew [ <-Ex | <-Ey | <-Ez ]; clear x y z Ex Ey Ez.
  enough (f (a ⊔ (b ⊓ c)) = f ((a ⊔ b) ⊓ (a ⊔ c))) as P by (revert P; now rewrite_preserves f).
  apply (is_fun f _ _).
  exact (join_meet_distr_l (to_subset a:U) (to_subset b:U) (to_subset c:U)).
+ intros [x elx][y ely][z elz]. change (x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)). revert elx ely elz. unfold_image.
  intros [a[Ex ela]][b[Ey elb]][c[Ez elc]]. rew [ <-Ex | <-Ey | <-Ez ]; clear x y z Ex Ey Ez.
  enough (f (a ⊓ (b ⊔ c)) = f ((a ⊓ b) ⊔ (a ⊓ c))) as P by (revert P; now rewrite_preserves f).
  apply (is_fun f _ _).
  exact (meet_join_distr_l (to_subset a:U) (to_subset b:U) (to_subset c:U)).
Qed.
Global Hint Extern 2 (DistributiveLattice (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_sub_lattice_distr_lattice : typeclass_instances.

