Require Export interfaces.subalgebra theory.rings theory.subgroups.
Require Import sprop.
Require Import interfaces.set theory.set theory.projected_set.
Require Import logic.aprop.
Require Import easy replc rewrite_preserves.

Local Open Scope mult_scope.

Definition alt_Build_AdditiveSubSemiGroup@{u} : ∀ `{AdditiveNonComSemiGroup@{u} X} {Y:𝒫 X},
  (∀ x y, x ∊ Y ⊠ y ∊ Y ⊸ x + y ∊ Y) → AdditiveSubSemiGroup Y
:= @alt_Build_SubSemiGroup.

Definition alt_Build_MultiplicativeSubSemiGroup@{u} : ∀ `{MultiplicativeSemiGroup@{u} X} {Y:𝒫 X},
  (∀ x y, x ∊ Y ⊠ y ∊ Y ⊸ x · y ∊ Y) → MultiplicativeSubSemiGroup Y
:= @alt_Build_SubSemiGroup.

Definition alt_Build_AdditiveSubMonoid@{u} : ∀ `{AdditiveNonComMonoid@{u} X} {Y:𝒫 X},
  (∀ x y, x ∊ Y ⊠ y ∊ Y ⊸ x + y ∊ Y)
 → 0 ∊ Y
 → AdditiveSubMonoid Y
:= @alt_Build_SubMonoid.

Definition alt_Build_MultiplicativeSubMonoid@{u} : ∀ `{MultiplicativeMonoid@{u} X} {Y:𝒫 X},
  (∀ x y, x ∊ Y ⊠ y ∊ Y ⊸ x · y ∊ Y)
 → 1 ∊ Y
 → MultiplicativeSubMonoid Y
:= @alt_Build_SubMonoid.

Definition alt_Build_AdditiveSubGroup@{u} : ∀ `{AdditiveNonComGroup@{u} X} {Y:𝒫 X},
  (∀ x y, x ∊ Y ⊠ y ∊ Y ⊸ x + y ∊ Y)
 → 0 ∊ Y
 → (∀ x, x ∊ Y ⊸ -x ∊ Y)
 → AdditiveSubGroup Y
:= @alt_Build_SubGroup.


Global Hint Extern 4 (apos (_ + _ ∊ _)) => simple notypeclasses refine  (andl (sub_add_sg_closed _ _) _) : typeclass_instances.
Global Hint Extern 4 (apos (_ · _ ∊ _)) => simple notypeclasses refine  (andl (sub_mul_sg_closed _ _) _) : typeclass_instances.
Global Hint Extern 4 (apos (0 ∊ _)) => simple notypeclasses refine sub_add_zero_closed : typeclass_instances.
Global Hint Extern 4 (apos (1 ∊ _)) => simple notypeclasses refine sub_mul_one_closed : typeclass_instances.
Global Hint Extern 4 (apos (-_ ∊ _)) => simple notypeclasses refine (andl (sub_add_neg_closed _) _) : typeclass_instances.

Definition full_add_sub_sg@{u}  : ∀ `{AdditiveNonComSemiGroup@{u} G}, AdditiveSubSemiGroup (full_subset G) := @full_sub_sg.
Definition full_add_sub_mon@{u} : ∀ `{AdditiveNonComMonoid@{u} M}, AdditiveSubMonoid (full_subset M) := @full_sub_mon.
Definition full_add_sub_grp@{u} : ∀ `{AdditiveNonComGroup@{u}  G}, AdditiveSubGroup  (full_subset G) := @full_sub_grp.
Definition full_add_normal_sub_grp@{u} : ∀ `{AdditiveNonComGroup@{u} G}, AdditiveNormalSubGroup (full_subset G) := @full_normal_sub_grp.

Definition full_mul_sub_sg@{u}  : ∀ `{MultiplicativeSemiGroup@{u} G}, MultiplicativeSubSemiGroup (full_subset G) := @full_sub_sg.
Definition full_mul_sub_mon@{u} : ∀ `{MultiplicativeMonoid@{u}    M}, MultiplicativeSubMonoid    (full_subset M) := @full_sub_mon.

Global Hint Extern 2 (AdditiveSubSemiGroup (full_subset _)) => simple notypeclasses refine full_add_sub_sg  : typeclass_instances.
Global Hint Extern 2 (AdditiveSubMonoid    (full_subset _)) => simple notypeclasses refine full_add_sub_mon : typeclass_instances.
Global Hint Extern 2 (AdditiveSubGroup     (full_subset _)) => simple notypeclasses refine full_add_sub_grp : typeclass_instances.
Global Hint Extern 2 (AdditiveNormalSubGroup (full_subset _)) => simple notypeclasses refine full_add_normal_sub_grp : typeclass_instances.

Global Hint Extern 2 (MultiplicativeSubSemiGroup (full_subset _)) => simple notypeclasses refine full_mul_sub_sg  : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSubMonoid    (full_subset _)) => simple notypeclasses refine full_mul_sub_mon : typeclass_instances.


(** Substructure predicates respect equality of subsets. *)

Canonical Structure MultiplicativeSubSemiGroup_fun {G op} :=
  make_fun_alt (@MultiplicativeSubSemiGroup G op) (@SubSemiGroup_fun G op).

Canonical Structure MultiplicativeSubMonoid_fun {G op unit} :=
  make_fun_alt (@MultiplicativeSubMonoid G op unit) (@SubMonoid_fun G op unit).

Canonical Structure AdditiveSubMonoid_fun {G op unit} :=
  make_fun_alt (@AdditiveSubMonoid G op unit) (@SubMonoid_fun G op unit).

Canonical Structure AdditiveSubGroup_fun {G op unit i} :=
  make_fun_alt (@AdditiveSubGroup G op unit i) (@SubGroup_fun G op unit i).

Canonical Structure AdditiveNormalSubGroup_fun {G op unit i} :=
  make_fun_alt (@AdditiveNormalSubGroup G op unit i) (@NormalSubGroup_fun G op unit i).

(** Induced operations on subsets when viewed as sets. *)

Definition sub_add_sg_plus@{u} : ∀ `{@AdditiveSubSemiGroup@{u} G Gplus H}, Plus H := @sub_semigroup_op.
Definition sub_mul_sg_mult@{u} : ∀ `{@MultiplicativeSubSemiGroup@{u} G Gmult H}, Mult H := @sub_semigroup_op.

Definition sub_add_zero@{u} : ∀ `{@AdditiveSubMonoid@{u} M Mplus Mzero N}, Zero N := @sub_monoid_unit.
Definition sub_mul_one@{u}  : ∀ `{@MultiplicativeSubMonoid@{u} M Mmult Mone N}, One N := @sub_monoid_unit.

Definition sub_add_negate@{u} `{@AdditiveSubGroup@{u} G Gplus Gzero Gnegate H} : Negate H := sub_star_semigroup_inv H.

Global Hint Extern 2 (Plus (subset_to_set ?H)) => refine (sub_add_sg_plus (H:=H)) : typeclass_instances.
Global Hint Extern 2 (Mult (subset_to_set ?H)) => refine (sub_mul_sg_mult (H:=H)) : typeclass_instances.
Global Hint Extern 2 (Zero (subset_to_set ?H)) => refine (sub_add_zero (N:=H)) : typeclass_instances.
Global Hint Extern 2 (One  (subset_to_set ?H)) => refine (sub_mul_one (N:=H)) : typeclass_instances.
Global Hint Extern 2 (Negate (subset_to_set ?H)) => refine (sub_add_negate (H:=H)) : typeclass_instances.

(** Sub structures are instances of structures when viewed as sets. *)

Definition sub_add_semigroup_semigroup@{u} : ∀ `{@AdditiveSubSemiGroup@{u} G Gplus H}, AdditiveNonComSemiGroup H := @sub_semigroup_semigroup.
Definition sub_add_semigroup_com_semigroup@{u} : ∀ `{P:AdditiveSemiGroup@{u} G} {H:𝒫 G} `{!AdditiveSubSemiGroup H}, AdditiveSemiGroup H := @sub_semigroup_com_semigroup.
Definition sub_add_monoid_monoid@{u} : ∀ `{@AdditiveSubMonoid@{u} M Mplus Mzero N}, AdditiveNonComMonoid N := @sub_monoid_monoid.
Definition sub_add_monoid_com_monoid@{u} : ∀ `{P:AdditiveMonoid@{u} M} {N:𝒫 M} `{!AdditiveSubMonoid N}, AdditiveMonoid N := @sub_monoid_com_monoid.
Definition sub_add_group_group@{u} : ∀ `{@AdditiveSubGroup@{u} G Gplus Gzero Gnegate H}, AdditiveNonComGroup H := @sub_group_group.
Definition sub_add_group_abgroup@{u} : ∀ `{P:AdditiveGroup@{u} G} {H:𝒫 G} `{!AdditiveSubGroup H}, AdditiveGroup H := @sub_group_abgroup.

Global Hint Extern 2 (AdditiveNonComSemiGroup (subset_to_set _)) => simple notypeclasses refine sub_add_semigroup_semigroup : typeclass_instances.
Global Hint Extern 2 (AdditiveSemiGroup (subset_to_set _)) => simple notypeclasses refine sub_add_semigroup_com_semigroup : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComMonoid (subset_to_set _)) => simple notypeclasses refine sub_add_monoid_monoid : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid (subset_to_set _)) => simple notypeclasses refine sub_add_monoid_com_monoid : typeclass_instances.
Global Hint Extern 2 (AdditiveNonComGroup (subset_to_set _)) => simple notypeclasses refine sub_add_group_group : typeclass_instances.
Global Hint Extern 2 (AdditiveGroup (subset_to_set _)) => simple notypeclasses refine sub_add_group_abgroup : typeclass_instances.

Definition sub_mul_semigroup_semigroup@{u} : ∀ `{@MultiplicativeSubSemiGroup@{u} G Gmult H}, MultiplicativeSemiGroup H := @sub_semigroup_semigroup.
Definition sub_mul_monoid_monoid@{u} : ∀ `{@MultiplicativeSubMonoid@{u} M Mmult Mone N}, MultiplicativeMonoid N := @sub_monoid_monoid.
Definition sub_mul_monoid_com_monoid@{u} : ∀ `{P:MultiplicativeComMonoid@{u} M} {N:𝒫 M} `{!MultiplicativeSubMonoid N}, MultiplicativeComMonoid N := @sub_monoid_com_monoid.

Global Hint Extern 2 (MultiplicativeSemiGroup (subset_to_set _)) => simple notypeclasses refine sub_mul_semigroup_semigroup : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid (subset_to_set _)) => simple notypeclasses refine sub_mul_monoid_monoid : typeclass_instances.
Global Hint Extern 2 (MultiplicativeComMonoid (subset_to_set _)) => simple notypeclasses refine sub_mul_monoid_com_monoid : typeclass_instances.

Definition sub_add_abgroup_normal@{u} : ∀ `{P:AdditiveGroup@{u} G} {H:𝒫 G} `{!AdditiveSubGroup H}, AdditiveNormalSubGroup H := @sub_abgroup_normal.
Global Hint Extern 4 (AdditiveNormalSubGroup _) => simple notypeclasses refine sub_add_abgroup_normal : typeclass_instances.

(** Inclusion of the substructure is structure preserving *)

Definition from_add_sub_semigroup@{u} : ∀ `{@AdditiveSubSemiGroup@{u} G Gplus H}, AdditiveSemiGroup_Morphism (from_subset H) := @from_sub_semigroup.
Definition from_mul_sub_semigroup@{u} : ∀ `{@MultiplicativeSubSemiGroup@{u} G Gmult H}, MultiplicativeSemiGroup_Morphism (from_subset H) := @from_sub_semigroup.
Global Hint Extern 2 (AdditiveSemiGroup_Morphism (from_subset _)) => simple notypeclasses refine from_add_sub_semigroup : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSemiGroup_Morphism (from_subset _)) => simple notypeclasses refine from_mul_sub_semigroup : typeclass_instances.

Definition from_add_sub_monoid@{u} : ∀ `{@AdditiveSubMonoid@{u} G Gplus Gzero H}, AdditiveMonoid_Morphism (from_subset H) := @from_sub_monoid.
Definition from_mul_sub_monoid@{u} : ∀ `{@MultiplicativeSubMonoid@{u} G Gmult Gone H}, MultiplicativeMonoid_Morphism (from_subset H) := @from_sub_monoid.
Global Hint Extern 2 (AdditiveMonoid_Morphism (from_subset _)) => simple notypeclasses refine from_add_sub_monoid : typeclass_instances.
Global Hint Extern 2 (Zero_Pointed_Morphism (from_subset _)) => simple notypeclasses refine from_add_sub_monoid : typeclass_instances.
Global Hint Extern 2 (MultiplicativeMonoid_Morphism (from_subset _)) => simple notypeclasses refine from_mul_sub_monoid : typeclass_instances.
Global Hint Extern 2 (One_Pointed_Morphism (from_subset _)) => simple notypeclasses refine from_mul_sub_monoid : typeclass_instances.

(** Image and preimage *)
Import image_notation.

Definition image_add_sub_sg@{u} : ∀ {X Y : set@{u}} `{@AdditiveSemiGroup_Morphism X Y Xop Yop f} {U:𝒫 X} `{!AdditiveSubSemiGroup U}, AdditiveSubSemiGroup (f⁎ U) := @image_sub_sg.
Definition image_mul_sub_sg@{u} : ∀ {X Y : set@{u}} `{@MultiplicativeSemiGroup_Morphism X Y Xop Yop f} {U:𝒫 X} `{!MultiplicativeSubSemiGroup U}, MultiplicativeSubSemiGroup (f⁎ U) := @image_sub_sg.
Global Hint Extern 2 (AdditiveSubSemiGroup (func_op _⁎ _)) => simple notypeclasses refine image_add_sub_sg : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSubSemiGroup (func_op _⁎ _)) => simple notypeclasses refine image_mul_sub_sg : typeclass_instances.

Definition preimage_add_sub_sg@{u} : ∀ {X Y : set@{u}} `{@AdditiveSemiGroup_Morphism X Y Xop Yop f} {U:𝒫 Y} `{!AdditiveSubSemiGroup U}, AdditiveSubSemiGroup (f* U) := @preimage_sub_sg.
Definition preimage_mul_sub_sg@{u} : ∀ {X Y : set@{u}} `{@MultiplicativeSemiGroup_Morphism X Y Xop Yop f} {U:𝒫 Y} `{!MultiplicativeSubSemiGroup U}, MultiplicativeSubSemiGroup (f* U) := @preimage_sub_sg.
Global Hint Extern 2 (AdditiveSubSemiGroup (func_op _* _)) => simple notypeclasses refine preimage_add_sub_sg : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSubSemiGroup (func_op _* _)) => simple notypeclasses refine preimage_mul_sub_sg : typeclass_instances.

Definition image_add_sub_mon@{u} : ∀ {X Y : set@{u}} `{@AdditiveMonoid_Morphism X Y Xop Xe Yop Ye f} {U:𝒫 X} `{!AdditiveSubMonoid U}, AdditiveSubMonoid (f⁎ U) := @image_sub_mon.
Definition image_mul_sub_mon@{u} : ∀ {X Y : set@{u}} `{@MultiplicativeMonoid_Morphism X Y Xop Xe Yop Ye f} {U:𝒫 X} `{!MultiplicativeSubMonoid U}, MultiplicativeSubMonoid (f⁎ U) := @image_sub_mon.
Global Hint Extern 2 (AdditiveSubMonoid (func_op _⁎ _)) => simple notypeclasses refine image_add_sub_mon : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSubMonoid (func_op _⁎ _)) => simple notypeclasses refine image_mul_sub_mon : typeclass_instances.

Definition preimage_add_sub_mon@{u} : ∀ {X Y : set@{u}} `{@AdditiveMonoid_Morphism X Y Xop Xe Yop Ye f} {U:𝒫 Y} `{!AdditiveSubMonoid U}, AdditiveSubMonoid (f* U) := @preimage_sub_mon.
Definition preimage_mul_sub_mon@{u} : ∀ {X Y : set@{u}} `{@MultiplicativeMonoid_Morphism X Y Xop Xe Yop Ye f} {U:𝒫 Y} `{!MultiplicativeSubMonoid U}, MultiplicativeSubMonoid (f* U) := @preimage_sub_mon.
Global Hint Extern 2 (AdditiveSubMonoid (func_op _* _)) => simple notypeclasses refine preimage_add_sub_mon : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSubMonoid (func_op _* _)) => simple notypeclasses refine preimage_mul_sub_mon : typeclass_instances.

Definition image_add_sub_grp@{u} : ∀ {X Y:set@{u}} `{AdditiveNonComGroup X} `{AdditiveNonComGroup Y} {f:X ⇾ Y} `{!AdditiveSemiGroup_Morphism f} {U:𝒫 X} `{!AdditiveSubGroup U}, AdditiveSubGroup (f⁎ U) := @image_sub_grp.
Global Hint Extern 2 (AdditiveSubGroup (func_op _⁎ _)) => simple notypeclasses refine image_add_sub_grp : typeclass_instances.

Definition preimage_add_sub_grp@{u} : ∀ {X Y:set@{u}} `{AdditiveNonComGroup X} `{AdditiveNonComGroup Y} {f:X ⇾ Y} `{!AdditiveSemiGroup_Morphism f} {U:𝒫 Y} `{!AdditiveSubGroup U}, AdditiveSubGroup (f* U) := @preimage_sub_grp.
Global Hint Extern 2 (AdditiveSubGroup (func_op _* _)) => simple notypeclasses refine preimage_add_sub_grp : typeclass_instances.

Definition image_add_com_sg : ∀ `{@AdditiveSemiGroup_Morphism X Y Xop Yop f} {U:𝒫 X} `{!AdditiveSubSemiGroup U, !AdditiveSemiGroup U},
   AdditiveSemiGroup (subset_to_set (f⁎ U )) := @image_com_sg.
Definition image_add_com_mon : ∀ `{@Monoid_Morphism X Y Xop Xe Yop Ye f} {U:𝒫 X} `{!AdditiveSubMonoid U, !AdditiveMonoid U},
  AdditiveMonoid (subset_to_set (f⁎ U)) := @image_com_mon.
Global Hint Extern 2 (AdditiveSemiGroup (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_add_com_sg : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_add_com_mon : typeclass_instances.

Definition image_add_abgrp@{u} : ∀ {X Y:set@{u}} `{AdditiveNonComGroup X} `{AdditiveNonComGroup Y}
  {f:X ⇾ Y} `{!AdditiveSemiGroup_Morphism f} {U:𝒫 X} `{!AdditiveSubGroup U, !AdditiveGroup U},
  AdditiveGroup (subset_to_set (f⁎ U)) := @image_abgrp.

Global Hint Extern 2 (AdditiveSemiGroup (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_add_com_sg : typeclass_instances.
Global Hint Extern 2 (AdditiveMonoid (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_add_com_mon : typeclass_instances.
Global Hint Extern 2 (AdditiveGroup (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_add_abgrp : typeclass_instances.

Definition image_mul_com_mon : ∀ `{@MultiplicativeMonoid_Morphism X Y Xop Xe Yop Ye f} {U:𝒫 X} `{!MultiplicativeSubMonoid U, !MultiplicativeComMonoid U},
  MultiplicativeComMonoid (subset_to_set (f⁎ U)) := @image_com_mon.
Global Hint Extern 2 (MultiplicativeComMonoid (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_mul_com_mon : typeclass_instances.


(** Rings *)

Coercion SubNearRig_SubNearRg   `{H:@SubNearRig  R p m z o   S} : SubNearRg  S.  Proof. now split. Qed.
Coercion SubNearRng_SubNearRg   `{H:@SubNearRng  R p m z   n S} : SubNearRg  S.  Proof. now split. Qed.
Coercion SubNearRing_SubNearRig `{H:@SubNearRing R p m z o n S} : SubNearRig S.  Proof. now split. Qed.
Coercion SubNearRing_SubNearRng `{H:@SubNearRing R p m z o n S} : SubNearRng S.  Proof. now split. Qed.

Lemma alt_Build_SubNearRg   `{P:@NearRg   R p m z    } (S: 𝒫 R) : AdditiveSubMonoid S → MultiplicativeSubSemiGroup S → SubNearRg   S.  Proof. intros; now split. Qed.
Lemma alt_Build_SubNearRig  `{P:@NearRig  R p m z o  } (S: 𝒫 R) : AdditiveSubMonoid S → MultiplicativeSubMonoid    S → SubNearRig  S.  Proof. intros; now split. Qed.
Lemma alt_Build_SubNearRng  `{P:@NearRng  R p m z   n} (S: 𝒫 R) : AdditiveSubGroup  S → MultiplicativeSubSemiGroup S → SubNearRng  S.  Proof. intros; now split. Qed.
Lemma alt_Build_SubNearRing `{P:@NearRing R p m z o n} (S: 𝒫 R) : AdditiveSubGroup  S → MultiplicativeSubMonoid    S → SubNearRing S.  Proof. intros; now split. Qed.

Lemma alt_Build_SubNearRg2   `{P:@NearRg   R p m z    } (S: 𝒫 R) :
   (∀ x y, x ∊ S ⊠ y ∊ S ⊸ x + y ∊ S)
 → (∀ x y, x ∊ S ⊠ y ∊ S ⊸ x · y ∊ S)
 → 0 ∊ S
 → SubNearRg S.
Proof. intros; apply alt_Build_SubNearRg. now apply alt_Build_AdditiveSubMonoid. now apply alt_Build_MultiplicativeSubSemiGroup. Qed.

Lemma alt_Build_SubNearRig2   `{P:@NearRig  R p m z o  } (S: 𝒫 R) :
   (∀ x y, x ∊ S ⊠ y ∊ S ⊸ x + y ∊ S)
 → (∀ x y, x ∊ S ⊠ y ∊ S ⊸ x · y ∊ S)
 → 0 ∊ S
 → 1 ∊ S
 → SubNearRig S.
Proof. intros; apply alt_Build_SubNearRig. now apply alt_Build_AdditiveSubMonoid. now apply alt_Build_MultiplicativeSubMonoid. Qed.

Lemma alt_Build_SubNearRng2   `{P:@NearRng  R p m z   n} (S: 𝒫 R) :
   (∀ x y, x ∊ S ⊠ y ∊ S ⊸ x + y ∊ S)
 → (∀ x y, x ∊ S ⊠ y ∊ S ⊸ x · y ∊ S)
 → (∀ x, x ∊ S ⊸ -x ∊ S)
 → 0 ∊ S
 → SubNearRng S.
Proof. intros; apply alt_Build_SubNearRng. now apply alt_Build_AdditiveSubGroup. now apply alt_Build_MultiplicativeSubSemiGroup. Qed.
Require Import tactics.misc.
Require Import orders.subset.
Require Import orders.orders.
Lemma alt_Build_SubNearRing2   `{P:@NearRing R p m z o n} (S: 𝒫 R) :
   (∀ x y, x ∊ S ⊠ y ∊ S ⊸ x + y ∊ S)
 → (∀ x y, x ∊ S ⊠ y ∊ S ⊸ x · y ∊ S)
 → (∀ x, x ∊ S ⊸ -x ∊ S)
 → 1 ∊ S
 → SubNearRing S.
Proof. intros Hp Hm Hn ?; apply alt_Build_SubNearRing; [| now apply alt_Build_MultiplicativeSubMonoid ].
  apply alt_Build_AdditiveSubGroup; trivial.
  rew <-(plus_negate_r 1). apply Hp; split; trivial. now apply Hn.
Qed.


Lemma full_sub_near_rg   `{NearRg   R} : SubNearRg   (full_subset R).  Proof. now split. Qed.
Lemma full_sub_near_rig  `{NearRig  R} : SubNearRig  (full_subset R).  Proof. now split. Qed.
Lemma full_sub_near_rng  `{NearRng  R} : SubNearRng  (full_subset R).  Proof. now split. Qed.
Lemma full_sub_near_ring `{NearRing R} : SubNearRing (full_subset R).  Proof. now split. Qed.
Global Hint Extern 2 (SubNearRg   (full_subset _)) => simple notypeclasses refine full_sub_near_rg   : typeclass_instances.
Global Hint Extern 2 (SubNearRig  (full_subset _)) => simple notypeclasses refine full_sub_near_rig  : typeclass_instances.
Global Hint Extern 2 (SubNearRng  (full_subset _)) => simple notypeclasses refine full_sub_near_rng  : typeclass_instances.
Global Hint Extern 2 (SubNearRing (full_subset _)) => simple notypeclasses refine full_sub_near_ring : typeclass_instances.


(** Substructure predicates respect equality of subsets. *)

Lemma SubNearRg_proper_impl {R p m z} S₁ S₂
  : S₁ = S₂ → impl (@SubNearRg R p m z S₁, SubNearRg S₂).
Proof. intros E P; split; try exact _; now rew <-E. Qed.
Canonical Structure SubNearRg_fun {R p m z} :=
  make_weak_spred (@SubNearRg R p m z) SubNearRg_proper_impl.

Lemma SubNearRig_proper_impl {R p m z o} S₁ S₂
  : S₁ = S₂ → impl (@SubNearRig R p m z o S₁, SubNearRig S₂).
Proof. intros E P; split; try exact _; now rew <-E. Qed.
Canonical Structure SubNearRig_fun {R p m z o} :=
  make_weak_spred (@SubNearRig R p m z o) SubNearRig_proper_impl.

Lemma SubNearRng_proper_impl {R p m z n} S₁ S₂
  : S₁ = S₂ → impl (@SubNearRng R p m z n S₁, SubNearRng S₂).
Proof. intros E P; split; try exact _; now rew <-E. Qed.
Canonical Structure SubNearRng_fun {R p m z n} :=
  make_weak_spred (@SubNearRng R p m z n) SubNearRng_proper_impl.

Lemma SubNearRing_proper_impl {R p m z o n} S₁ S₂
  : S₁ = S₂ → impl (@SubNearRing R p m z o n S₁, SubNearRing S₂).
Proof. intros E P; split; try exact _; now rew <-E. Qed.
Canonical Structure SubNearRing_fun {R p m z o n} :=
  make_weak_spred (@SubNearRing R p m z o n) SubNearRing_proper_impl.

(** Sub structures are instances of structures when viewed as sets. *)

Lemma sub_near_rg_near_rg `{@SubNearRg R p m z S} : NearRg S.
Proof. split; try exact _.
+ intros x y. exact (plus_mult_distr_r (x:R) (y:R)).
+ intros x. exact (mult_0_l (x:R)).
Qed.
Global Hint Extern 2 (NearRg (subset_to_set _)) => simple notypeclasses refine sub_near_rg_near_rg : typeclass_instances.

Lemma sub_near_rig_near_rig `{@SubNearRig R p m z o S} : NearRig S.
Proof. now split. Qed.
Global Hint Extern 2 (NearRig (subset_to_set _)) => simple notypeclasses refine sub_near_rig_near_rig : typeclass_instances.

Lemma sub_near_rng_near_rng `{@SubNearRng R p m z n S} : NearRng S.
Proof. now split. Qed.
Global Hint Extern 2 (NearRng (subset_to_set _)) => simple notypeclasses refine sub_near_rng_near_rng : typeclass_instances.

Lemma sub_near_ring_near_ring `{@SubNearRing R p m z o n S} : NearRing S.
Proof. now split. Qed.
Global Hint Extern 2 (NearRing (subset_to_set _)) => simple notypeclasses refine sub_near_ring_near_ring : typeclass_instances.

Lemma sub_near_rg_rg `{@Rg R p m z} {S:𝒫 R} `{!SubNearRg S} : Rg S.
Proof. split; try exact _. split; try exact _.
+ intros a b c. exact (plus_mult_distr_l (a:R) (b:R) (c:R)).
+ intros x. exact (mult_0_r (x:R)).
Qed.
Global Hint Extern 2 (Rg (subset_to_set _)) => simple notypeclasses refine sub_near_rg_rg : typeclass_instances.

Lemma sub_near_rig_rig `{@Rig R p m z o} {S:𝒫 R} `{!SubNearRig S} : Rig S.
Proof. now split. Qed.
Global Hint Extern 2 (Rig (subset_to_set _)) => simple notypeclasses refine sub_near_rig_rig : typeclass_instances.

Lemma sub_near_rng_rng `{@Rng R p m z n} {S:𝒫 R} `{!SubNearRng S} : Rng S.
Proof. now split. Qed.
Global Hint Extern 2 (Rng (subset_to_set _)) => simple notypeclasses refine sub_near_rng_rng : typeclass_instances.

Lemma sub_near_ring_ring `{@Ring R p m z o n} {S:𝒫 R} `{!SubNearRing S} : Ring S.
Proof. now split. Qed.
Global Hint Extern 2 (Ring (subset_to_set _)) => simple notypeclasses refine sub_near_ring_ring : typeclass_instances.

Lemma sub_near_rig_com_rig `{@CommutativeRig R p m z o} {S:𝒫 R} `{!SubNearRig S} : CommutativeRig S.
Proof. now split. Qed.
Global Hint Extern 2 (CommutativeRig (subset_to_set _)) => simple notypeclasses refine sub_near_rig_com_rig : typeclass_instances.

Lemma sub_near_ring_com_ring `{@CommutativeRing R p m z o n} {S:𝒫 R} `{!SubNearRing S} : CommutativeRing S.
Proof. now split. Qed.
Global Hint Extern 2 (CommutativeRing (subset_to_set _)) => simple notypeclasses refine sub_near_ring_com_ring : typeclass_instances.

(** Inclusion of the substructure is structure preserving *)

Lemma from_sub_near_rg `{@SubNearRg R p m z S} : Rg_Morphism (from_subset S).
Proof. now split. Qed.
Global Hint Extern 2 (Rg_Morphism (from_subset _)) => simple notypeclasses refine from_sub_near_rg : typeclass_instances.

Lemma from_sub_near_rig `{@SubNearRig R p m z o S} : Rig_Morphism (from_subset S).
Proof. now split. Qed.
Global Hint Extern 2 (Rig_Morphism (from_subset _)) => simple notypeclasses refine from_sub_near_rig : typeclass_instances.

(** Image and preimage *)

Lemma    image_sub_near_rg `{@Rg_Morphism X Y pX pY mX mY zX zY f} {U:𝒫 X} `{!SubNearRg U, !NearRg Y} : SubNearRg (f⁎ U).  Proof. now split. Qed.
Lemma preimage_sub_near_rg `{@Rg_Morphism X Y pX pY mX mY zX zY f} {U:𝒫 Y} `{!SubNearRg U, !NearRg X} : SubNearRg (f* U).  Proof. now split. Qed.
Global Hint Extern 2 (SubNearRg (func_op _⁎ _)) => simple notypeclasses refine    image_sub_near_rg : typeclass_instances.
Global Hint Extern 2 (SubNearRg (func_op _* _)) => simple notypeclasses refine preimage_sub_near_rg : typeclass_instances.

Lemma    image_sub_near_rig `{@Rig_Morphism X Y pX pY mX mY zX zY oX oY f} {U:𝒫 X} `{!SubNearRig U, !NearRig Y} : SubNearRig (f⁎ U).  Proof. now split. Qed.
Lemma preimage_sub_near_rig `{@Rig_Morphism X Y pX pY mX mY zX zY oX oY f} {U:𝒫 Y} `{!SubNearRig U, !NearRig X} : SubNearRig (f* U).  Proof. now split. Qed.
Global Hint Extern 2 (SubNearRig (func_op _⁎ _)) => simple notypeclasses refine    image_sub_near_rg : typeclass_instances.
Global Hint Extern 2 (SubNearRig (func_op _* _)) => simple notypeclasses refine preimage_sub_near_rg : typeclass_instances.

Lemma    image_sub_near_rng `{@SubNearRng X pX mX zX nX U} `{@NearRng Y pY mY zY nY} {f:X ⇾ Y} `{!Rg_Morphism f} : SubNearRng (f⁎ U).  Proof. now split. Qed.
Lemma preimage_sub_near_rng `{@SubNearRng Y pY mY zY nY U} `{@NearRng X pX mX zX nX} {f:X ⇾ Y} `{!Rg_Morphism f} : SubNearRng (f* U).  Proof. now split. Qed.
Global Hint Extern 2 (SubNearRng (func_op _⁎ _)) => simple notypeclasses refine    image_sub_near_rng : typeclass_instances.
Global Hint Extern 2 (SubNearRng (func_op _* _)) => simple notypeclasses refine preimage_sub_near_rng : typeclass_instances.

Lemma    image_sub_near_ring `{@SubNearRing X pX mX zX oX nX U} `{@NearRing Y pY mY zY oY nY} {f:X ⇾ Y} `{!Rig_Morphism f} : SubNearRing (f⁎ U).  Proof. now split. Qed.
Lemma preimage_sub_near_ring `{@SubNearRing Y pY mY zY oY nY U} `{@NearRing X pX mX zX oX nX} {f:X ⇾ Y} `{!Rig_Morphism f} : SubNearRing (f* U).  Proof. now split. Qed.
Global Hint Extern 2 (SubNearRing (func_op _⁎ _)) => simple notypeclasses refine    image_sub_near_ring : typeclass_instances.
Global Hint Extern 2 (SubNearRing (func_op _* _)) => simple notypeclasses refine preimage_sub_near_ring : typeclass_instances.

Lemma image_sub_rg@{u} {X Y : set@{u}} `{@SubNearRg X pX mX zX U} `{!Rg U} `{@NearRg Y pY mY zY} {f:X ⇾ Y} `{!Rg_Morphism f} : Rg (subset_to_set (f⁎ U)).
Proof. split; try exact _. split; try exact _.
+ intros [x elx][y ely][z elz]. change (x · (y + z) = x · y + x · z). revert elx ely elz. unfold_image.
  intros [a[Ex ela]][b[Ey elb]][c[Ez elc]]. rew [ <-Ex | <-Ey | <-Ez ]; clear x y z Ex Ey Ez.
  enough (f (a · (b + c)) = f (a · b + a · c)) as P by (revert P; now rewrite_preserves f).
  apply (is_fun f _ _).
  exact (plus_mult_distr_l (to_subset a:U) (to_subset b:U) (to_subset c:U)).
+ intros [x elx]. change (x · 0 = 0). revert elx. unfold_image.
  intros [a[Ex ela]]. rew <-Ex; clear x Ex.
  enough (f (a · 0) = f 0) as P by (revert P; now rewrite_preserves f).
  apply (is_fun f _ _).
  exact (mult_0_r (to_subset a:U)).
Qed.
Global Hint Extern 2 (Rg (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_sub_rg : typeclass_instances.

Lemma image_sub_rig@{u} {X Y : set@{u}} `{@SubNearRig X pX mX zX oX U} `{!Rig U} `{@NearRig Y pY mY zY oY} {f:X ⇾ Y} `{!Rig_Morphism f} : Rig (subset_to_set (f⁎ U)).
Proof. now split. Qed.
Global Hint Extern 2 (Rig (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_sub_rig : typeclass_instances.

Lemma image_sub_rng@{u} {X Y : set@{u}} `{@SubNearRng X pX mX zX nX U} `{!Rng U} `{@NearRng Y pY mY zY nY} {f:X ⇾ Y} `{!Rg_Morphism f} : Rng (subset_to_set (f⁎ U)).
Proof. now split. Qed.
Global Hint Extern 2 (Rng (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_sub_rng : typeclass_instances.

Lemma image_sub_ring@{u} {X Y : set@{u}} `{@SubNearRing X pX mX zX oX nX U} `{!Ring U} `{@NearRing Y pY mY zY oY nY} {f:X ⇾ Y} `{!Rig_Morphism f} : Ring (subset_to_set (f⁎ U)).
Proof. now split. Qed.
Global Hint Extern 2 (Ring (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_sub_ring : typeclass_instances.

Lemma image_sub_com_rig@{u} {X Y : set@{u}} `{@SubNearRig X pX mX zX oX U} `{!CommutativeRig U} `{@NearRig Y pY mY zY oY} {f:X ⇾ Y} `{!Rig_Morphism f} : CommutativeRig (subset_to_set (f⁎ U)).
Proof. now split. Qed.
Global Hint Extern 2 (CommutativeRig (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_sub_com_rig : typeclass_instances.

Lemma image_sub_com_ring@{u} {X Y : set@{u}} `{@SubNearRing X pX mX zX oX nX U} `{!CommutativeRing U} `{@NearRing Y pY mY zY oY nY} {f:X ⇾ Y} `{!Rig_Morphism f} : CommutativeRing (subset_to_set (f⁎ U)).
Proof. now split. Qed.
Global Hint Extern 2 (CommutativeRing (subset_to_set (func_op _⁎ _))) => simple notypeclasses refine image_sub_com_ring : typeclass_instances.

(** Near Rings *)

Definition ZeroSymmetricPart N {m:Mult N} {z:Zero N} : 𝒫 N := { n : N | n · 0 = 0 }.
Local Notation "N ₀" := (ZeroSymmetricPart N) (at level 1, no associativity, format "N ₀").

Lemma ZeroSymmetricPart_SubNearRg `{NearRg N} : SubNearRg (N ₀).
Proof. apply alt_Build_SubNearRg2; [ intros x y .. |]; change (?n ∊ (N ₀)) with (n · 0 = 0).
+ rew (plus_mult_distr_r _ _ _). rew <-(plus_0_l 0) at 7. exact (is_fun (+) (_, _) (_, _)).
+ rew <-(transitivity (=) (x · y · 0) (x · 0) _). rew (aprod_com _ _) at 1.
  refine (aprod_proper_aimpl _ _). rew <-(associativity (·) _ _ _). exact (is_fun (x ·) _ _).
+ exact (mult_0_l _).
Qed.
Global Hint Extern 2 (SubNearRg (_ ₀)) => simple notypeclasses refine ZeroSymmetricPart_SubNearRg : typeclass_instances.
Global Hint Extern 2 (AdditiveSubMonoid (_ ₀)) => simple notypeclasses refine ZeroSymmetricPart_SubNearRg : typeclass_instances.
Global Hint Extern 2 (AdditiveSubSemiGroup (_ ₀)) => simple notypeclasses refine ZeroSymmetricPart_SubNearRg : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSubSemiGroup (_ ₀)) => simple notypeclasses refine ZeroSymmetricPart_SubNearRg : typeclass_instances.

Lemma ZeroSymmetricPart_SubNearRig `{NearRig N} : SubNearRig (N ₀).
Proof. apply alt_Build_SubNearRig2; try apply ZeroSymmetricPart_SubNearRg.
  exact (mult_1_l 0).
Qed.
Global Hint Extern 2 (SubNearRig (_ ₀)) => simple notypeclasses refine ZeroSymmetricPart_SubNearRig : typeclass_instances.
Global Hint Extern 2 (MultiplicativeSubMonoid (_ ₀)) => simple notypeclasses refine ZeroSymmetricPart_SubNearRig : typeclass_instances.

Lemma ZeroSymmetricPart_SubNearRng `{NearRng N} : SubNearRng (N ₀).
Proof. apply alt_Build_SubNearRng2; try apply ZeroSymmetricPart_SubNearRg.
  intros x. change (x · 0 = 0 ⊸ (-x) · 0 = 0).
  rew <-(negate_mult_distr_l x 0). rew <-negate_0 at 4.
  exact (is_fun (-) _ _).
Qed.
Global Hint Extern 2 (SubNearRng (_ ₀)) => simple notypeclasses refine ZeroSymmetricPart_SubNearRng : typeclass_instances.
Global Hint Extern 2 (AdditiveSubGroup (_ ₀)) => simple notypeclasses refine ZeroSymmetricPart_SubNearRng : typeclass_instances.

Lemma ZeroSymmetricPart_SubNearRing `{NearRing N} : SubNearRing (N ₀).
Proof. now split. Qed.
Global Hint Extern 2 (SubNearRing (_ ₀)) => simple notypeclasses refine ZeroSymmetricPart_SubNearRing : typeclass_instances.

